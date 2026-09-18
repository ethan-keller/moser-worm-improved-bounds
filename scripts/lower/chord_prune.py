"""Stream chord and LP pruning into a fresh, complete format 2 certificate."""

import gzip
from pathlib import Path
import resource
import tempfile

import chord_prune_core as A
from chord_prune_core import chord
from native import PrimitiveOracle, ChordLPOracle, build

from common import atomic_json, certificate_file, sha256_file
from export import chord_leaf_work
from prune import (
    interruptible,
    load_input,
    process_parts,
    collect_parts,
    worker_limits,
    write_gzip,
)

WORKER_ORACLE = None
WORKER_LP = None
LIMITS = chord.Limits()


def scan_tree(stream):
    """Count final witnesses in one bounded pass."""
    reader = chord.StreamReader(stream, version=2, limits=LIMITS)
    pending = [0]
    counts = dict(
        nodes=0,
        leaves=0,
        mixtures=0,
        depth=0,
        work=0,
        polygon_members=0,
        edges=0,
        fan_rows=0,
        annotated_leaves=0,
        chord_cuts=0,
        chord_side_rows=0,
        nonzero_checks=0,
        rotations=0,
    )
    while pending:
        depth = pending.pop()
        node = reader.read_node()
        counts["nodes"] += 1
        counts["depth"] = max(counts["depth"], depth)
        if type(node) is int:
            pending.extend((depth + 1, depth + 1))
            continue
        counts["leaves"] += 1
        counts["work"] += chord_leaf_work(node)
        if type(node) is chord.PlainLeaf:
            members = [(fan, chord.Terminal()) for fan in node.fans]
        else:
            counts["annotated_leaves"] += 1
            members = [(member.fan, member.witness) for member in node.members]
        counts["mixtures"] += len(members) > 1
        counts["polygon_members"] += len(members)
        counts["edges"] += sum(len(fan.labels) for fan, _ in members)
        todo = [(fan.labels, witness) for fan, witness in members]
        while todo:
            labels, witness = todo.pop()
            if type(witness) is chord.Terminal:
                if len(labels) > 5:
                    counts["fan_rows"] += 2 * len(labels) - 5
            elif type(witness) is chord.Rotate:
                counts["rotations"] += 1
                todo.append((chord.rotate_labels(labels, witness.offset), witness.child))
            else:
                left, right = chord.arcs(labels, witness.i, witness.j)
                counts["chord_cuts"] += 1
                counts["chord_side_rows"] += len(labels) - 2
                counts["nonzero_checks"] += 1
                todo.extend(((right, witness.right), (left, witness.left)))
    reader.finish()
    return counts


def process_part(job):
    directory, output, part = job
    source = certificate_file(directory, part["file"])
    raw = Path(output) / f"part{part['id']:06d}.bin"
    destination = raw.with_suffix(".bin.gz")
    with gzip.open(source, "rb") as inp, raw.open("w+b") as out:
        A.postprocess_stream(
            inp,
            out,
            part["box"],
            WORKER_ORACLE,
            chord_leaf_work,
            limits=LIMITS,
            input_version=1,
            lp=WORKER_LP,
            lp_min_leaves=2,
        )
    with raw.open("rb") as inp:
        counts = scan_tree(inp)
    write_gzip(raw, destination)
    raw.unlink()
    return {
        "id": part["id"],
        "box": part["box"],
        "path": part["path"],
        "format": 2,
        "complete": True,
        "file": destination.name,
        "sha256": sha256_file(destination),
        **counts,
    }


def worker_init(library, lp_library, memory_limit):
    global WORKER_ORACLE, WORKER_LP
    resource.setrlimit(resource.RLIMIT_AS, (memory_limit, memory_limit))
    WORKER_ORACLE = PrimitiveOracle(library)
    WORKER_LP = ChordLPOracle(lp_library)


def run(input: Path, output: Path, jobs: int):
    input, output = Path(input).resolve(), Path(output).resolve()
    if input == output or input in output.parents or output in input.parents:
        raise ValueError("input and output directories must be disjoint")
    upstream = load_input(input)
    jobs, memory_limit = worker_limits(jobs, len(upstream["parts"]))
    output.mkdir(parents=True)
    with (
        interruptible(),
        tempfile.TemporaryDirectory(dir=output, prefix=".chord-prune-") as temporary,
    ):
        work = Path(temporary)
        library, lp_library = build(work, "geometry"), build(work, "lp")
        records = process_parts(
            process_part,
            input,
            work,
            upstream["parts"],
            jobs,
            worker_init,
            (library, lp_library, memory_limit),
            stage="Lower chord pruning",
        )
        metadata = collect_parts(output, work, upstream, records, 2)
    atomic_json(output / "manifest.json", metadata)
    return metadata
