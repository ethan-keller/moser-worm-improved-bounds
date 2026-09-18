"""Stream chord pruning using geometry checks and LP proposals.

Replacements cover whole parent boxes and reduce the work estimate.
Every final certificate requires independent Lean kernel checking.
"""

from dataclasses import dataclass
from itertools import zip_longest

import chord
from interval import ONE

POOL_LIMIT = 16
LP_CYCLE_LIMIT = 24


def checked_box(box):
    if len(box) != 9:
        raise ValueError("expected nine coordinate intervals")
    result = []
    for interval in box:
        if len(interval) != 2:
            raise ValueError("invalid coordinate interval")
        lo, hi = interval
        if type(lo) is not int or type(hi) is not int or lo > hi:
            raise ValueError("invalid coordinate bounds")
        result.append((lo, hi))
    return tuple(result)


def split_box(box, axis):
    lo, hi = box[axis]
    mid = (lo + hi) // 2
    if not lo < mid < hi:
        raise ValueError("input splits an indivisible interval")
    return (
        box[:axis] + ((lo, mid),) + box[axis + 1 :],
        box[:axis] + ((mid, hi),) + box[axis + 1 :],
    )


def fan_key(fans):
    return tuple((fan.weight, fan.labels) for fan in fans)


def leaf_fans(leaf):
    if type(leaf) is chord.PlainLeaf:
        return leaf.fans
    return tuple(member.fan for member in leaf.members)


def geometry_valid(oracle, labels, witness):
    """Recheck an explicitly stored witness using prepared C primitives."""
    lower = oracle.fan_lower_bound
    if type(witness) is chord.Terminal:
        if len(labels) <= 5:
            return True
        a, b = labels[:2]
        return all(lower(a, b, k) > 0 for k in labels[2:]) and all(
            lower(a, x, y) > 0 for x, y in zip(labels[2:-1], labels[3:])
        )
    if type(witness) is chord.Rotate:
        return geometry_valid(oracle, chord.rotate_labels(labels, witness.offset), witness.child)
    if type(witness) is not chord.Cut:
        raise ValueError("unknown chord witness")
    left, right = chord.arcs(labels, witness.i, witness.j)
    a, b = labels[witness.i], labels[witness.j]
    nz = witness.nonzero
    if type(nz) is chord.Coordinate:
        good = oracle.coordinate_nonzero(a, b)
    elif type(nz) is chord.Side:
        good = (lower(a, nz.label, b) if nz.reversed else lower(a, b, nz.label)) > 0
    else:
        raise ValueError("unknown nonzero witness")
    tests = [(a, k, b) if witness.positive_right else (a, b, k) for k in left[1:-1]] + [
        (a, b, k) if witness.positive_right else (a, k, b) for k in right[1:-1]
    ]
    return (
        good
        and all(lower(*t) >= 0 for t in tests)
        and geometry_valid(oracle, left, witness.left)
        and geometry_valid(oracle, right, witness.right)
    )


def candidate_pool(left, right):
    """Interleave and deduplicate candidate witnesses from both children."""
    result, seen = [], set()
    for pair in zip_longest(left, right):
        for fans in pair:
            if fans is not None and fan_key(fans) not in seen:
                result.append(fans)
                seen.add(fan_key(fans))
                if len(result) == POOL_LIMIT:
                    return tuple(result)
    return tuple(result)


class Prepared:
    """One prepared oracle box; all caches die before moving to another box.

    Oracle interface:
      prepare(box) -> bool
      area_lower_bound(tuple[Fan, ...]) -> signed integer scaled by ONE
      fan_lower_bound(a, b, c) -> max(direct, centered) signed lower bound
      coordinate_nonzero(a, b) -> bool for the actual chord on the whole box

    The C library may have process-global prepared state. Use one oracle per
    worker process, never concurrent Prepared objects backed by that library.
    """

    def __init__(self, oracle):
        self.oracle = oracle
        self.bounds = {}
        self.cuts = {}

    def lower(self, a, b, c):
        key = a, b, c
        if key not in self.bounds:
            value = self.oracle.fan_lower_bound(*key)
            if type(value) is not int:
                raise ValueError("oracle fan bound must be an integer")
            self.bounds[key] = value
        return self.bounds[key]

    def fan(self, labels):
        if len(labels) <= 5:
            return chord.Terminal()
        for offset in range(len(labels)):
            cycle = labels[offset:] + labels[:offset]
            a, b = cycle[:2]
            tests = [(a, b, k) for k in cycle[2:]]
            tests += [(a, x, y) for x, y in zip(cycle[2:-1], cycle[3:])]
            if all(self.lower(*triple) > 0 for triple in tests):
                terminal = chord.Terminal()
                return terminal if offset == 0 else chord.Rotate(offset, terminal)
        return None

    def cut(self, labels):
        if labels in self.cuts:
            return self.cuts[labels]
        if len(labels) <= 5:
            result = chord.Terminal()
            self.cuts[labels] = result
            return result
        n = len(labels)
        choices = [(i, j) for i in range(n) for j in range(i + 2, n) if not (i == 0 and j == n - 1)]
        choices.sort(key=lambda ij: abs(n + 2 - 2 * (ij[1] - ij[0] + 1)))
        for i, j in choices:
            a, b = labels[i], labels[j]
            left, right = chord.arcs(labels, i, j)
            for positive in (True, False):
                tests = [(a, k, b) if positive else (a, b, k) for k in left[1:-1]] + [
                    (a, b, k) if positive else (a, k, b) for k in right[1:-1]
                ]
                values = [self.lower(*triple) for triple in tests]
                if any(value < 0 for value in values):
                    continue
                strict = next((triple for triple, value in zip(tests, values) if value > 0), None)
                if strict is not None:
                    # Preserve the actual strict test's orientation explicitly.
                    nonzero = (
                        chord.Side(strict[2], False)
                        if strict[1] == b
                        else chord.Side(strict[1], True)
                    )
                else:
                    separated = self.oracle.coordinate_nonzero(a, b)
                    if type(separated) is not bool:
                        raise ValueError("oracle nonzero result must be a bool")
                    if not separated:
                        continue
                    nonzero = chord.Coordinate()
                lw = self.cut(left)
                if lw is None:
                    continue
                rw = self.cut(right)
                if rw is None:
                    continue
                result = chord.Cut(i, j, positive, nonzero, lw, rw)
                self.cuts[labels] = result
                return result
        self.cuts[labels] = None
        return None

    def leaf(self, fans):
        area = self.oracle.area_lower_bound(fans)
        if type(area) is not int:
            raise ValueError("oracle area bound must be an integer")
        if 1000 * area < 239 * ONE:
            return None
        members = []
        for fan in fans:
            witness = self.fan(fan.labels)
            if witness is None:
                witness = self.cut(fan.labels)
            if witness is None:
                return None
            members.append(chord.AnnotatedFan(fan, witness))
        return chord.AnnotatedLeaf(tuple(members))


@dataclass(frozen=True)
class Summary:
    leaves: int
    work: int
    depth: int
    pool: tuple


def parent_leaf(pool, leaves, work, box, oracle, cost, stats, lp, lp_min_leaves):
    """Try inherited weights, then one LP over up to 24 certified parent cycles."""
    ready = oracle.prepare(box)
    if type(ready) is not bool:
        raise ValueError("oracle prepare result must be a bool")
    if not ready:
        stats["prepare_rejections"] += 1
        return None
    context = Prepared(oracle)
    proposals = sorted(
        pool, key=lambda fans: (cost(chord.PlainLeaf(fans)), len(fans), fan_key(fans))
    )
    for fans in proposals:
        stats["probes"] += 1
        found = context.leaf(fans)
        if found is not None and cost(found) < work:
            stats["ordinary_collapses"] += 1
            return found
    if lp is None or leaves < lp_min_leaves:
        return None
    stats["lp_eligible"] += 1
    cycles, witnesses, seen = [], {}, set()
    for row in zip_longest(*pool):
        for fan in row:
            if fan is None or fan.labels in seen:
                continue
            labels = fan.labels
            seen.add(labels)
            witness = context.fan(labels)
            direct = witness is not None
            if witness is None:
                witness = context.cut(labels)
            if witness is None:
                continue
            if not geometry_valid(oracle, labels, witness):
                raise ValueError("constructed parent-cycle failed the C geometry check")
            cycles.append(labels)
            witnesses[labels] = witness
            stats["lp_geometry_cycles"] += 1
            stats["lp_cut_only_cycles"] += int(not direct)
            if len(cycles) == LP_CYCLE_LIMIT:
                break
        if len(cycles) == LP_CYCLE_LIMIT:
            break
    if len(cycles) < 2:
        return None
    stats["lp_parent_pools"] += 1
    if lp.prepare(box) is not True:
        raise ValueError("LP parent prepare failed")
    fans = lp.propose(cycles)
    if fans is None:
        return None
    chord.validate_fans(fans)
    if (
        any(f.weight <= 0 or f.labels not in witnesses for f in fans)
        or sum(f.weight for f in fans) != ONE
    ):
        raise ValueError("LP returned invalid weights or an uncertified cycle")
    if 1000 * oracle.area_lower_bound(fans) < 239 * ONE:
        raise ValueError("LP proposal failed exact area recheck")
    found = chord.AnnotatedLeaf(tuple(chord.AnnotatedFan(f, witnesses[f.labels]) for f in fans))
    if cost(found) >= work:
        stats["lp_work_rejected"] += 1
        return None
    stats["lp_collapses"] += 1
    stats["lp_new_weight_vectors"] += int(fan_key(fans) not in {fan_key(fs) for fs in pool})
    return found


def postprocess_stream(
    source,
    output,
    box,
    oracle,
    leaf_work,
    *,
    limits=chord.Limits(),
    input_version=1,
    lp=None,
    lp_min_leaves=8,
    progress=lambda stats: None,
):
    """Rewrite a complete v1/v2 stream into an unpublished, seekable v2 temporary.

    The injected work callback is export.chord_leaf_work and
    accepts PlainLeaf or AnnotatedLeaf. It must charge all cut/nonzero guards.
    LP is optional; its threshold counts surviving leaves in the two children.
    Output never subdivides an input leaf or changes a retained split.
    """
    if type(lp_min_leaves) is not int or lp_min_leaves < 2:
        raise ValueError("LP minimum must be an integer at least two")
    if source is output or output.tell() != 0:
        raise ValueError("output must be a distinct empty temporary stream")
    output.seek(0, 2)
    if output.tell() != 0:
        raise ValueError("output must be empty")
    output.seek(0)
    root = checked_box(box)
    reader = chord.StreamReader(source, version=input_version, limits=limits)
    stats = {
        "input_leaves": 0,
        "input_work": 0,
        "parents": 0,
        "probes": 0,
        "collapses": 0,
        "removed_leaves": 0,
        "prepare_rejections": 0,
        "ordinary_collapses": 0,
        "lp_eligible": 0,
        "lp_parent_pools": 0,
        "lp_geometry_cycles": 0,
        "lp_cut_only_cycles": 0,
        "lp_collapses": 0,
        "lp_work_rejected": 0,
        "lp_new_weight_vectors": 0,
    }
    lp_before = lp.stats() if lp is not None else {}

    def write(data):
        if output.tell() + len(data) > limits.input_bytes:
            raise ValueError("output byte limit")
        if output.write(data) != len(data):
            raise OSError("short output write")

    def cost(leaf):
        value = leaf_work(leaf)
        if type(value) is not int or value < 0:
            raise ValueError("work estimate must be a nonnegative integer")
        return value

    def emit_leaf(leaf):
        write(chord.write_leaf(leaf, version=2, limits=limits)[len(chord.MAGIC) :])

    def visit(current_box):
        begin = output.tell()
        node = reader.read_node()
        if type(node) is not int:
            fans = leaf_fans(node)
            work = cost(node)
            emit_leaf(node)
            stats["input_leaves"] += 1
            stats["input_work"] += work
            if stats["input_leaves"] % 4096 == 0:
                progress(
                    dict(
                        stats,
                        input_nodes=reader.nodes,
                        input_bytes=reader.offset,
                        temporary_output_bytes=output.tell(),
                    )
                )
            singles = sorted(
                ((chord.Fan(ONE, fan.labels),) for fan in fans),
                key=lambda fans: (cost(chord.PlainLeaf(fans)), fan_key(fans)),
            )
            return Summary(1, work, 0, candidate_pool((fans,), singles))
        write(bytes([node]))
        lb, rb = split_box(current_box, node)
        left = visit(lb)
        right = visit(rb)
        pool = candidate_pool(left.pool, right.pool)
        work = left.work + right.work
        stats["parents"] += 1
        found = parent_leaf(
            pool,
            left.leaves + right.leaves,
            work,
            current_box,
            oracle,
            cost,
            stats,
            lp,
            lp_min_leaves,
        )
        if found is not None:
            # Both children were consumed; replace exactly their output interval.
            output.seek(begin)
            output.truncate()
            emit_leaf(found)
            stats["collapses"] += 1
            stats["removed_leaves"] += left.leaves + right.leaves - 1
            return Summary(1, cost(found), 0, candidate_pool((leaf_fans(found),), pool))
        return Summary(left.leaves + right.leaves, work, 1 + max(left.depth, right.depth), pool)

    write(chord.MAGIC)
    result = visit(root)
    reader.finish()  # no complete result if the original root has trailing bytes
    if (
        reader.nodes != 2 * stats["input_leaves"] - 1
        or result.leaves + stats["removed_leaves"] != stats["input_leaves"]
    ):
        raise ValueError("input/output coverage accounting mismatch")
    if lp is not None:
        after = lp.stats()
        stats.update({"lp_solver_" + k: after[k] - lp_before[k] for k in after})
        if stats["lp_solver_solves"] > stats["lp_parent_pools"]:
            raise ValueError("LP solve budget exceeded")
    stats.update(
        {
            "complete": True,
            "input_nodes": reader.nodes,
            "output_nodes": 2 * result.leaves - 1,
            "output_leaves": result.leaves,
            "output_depth": result.depth,
            "output_work": result.work,
            "output_bytes": output.tell(),
            "input_bytes": reader.offset,
        }
    )
    progress(dict(stats))
    return stats
