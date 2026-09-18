"""Schedule bounded native chunks and assemble complete ordinary certificate trees."""

import concurrent.futures
import hashlib
import io
import json
from pathlib import Path
import shutil
import struct
import tempfile
import time

from certificate import read_exact, read_leaf
from common import Progress
from interval import ONE

TASK_MAGIC = b"MWTASK01"
CHUNK_MAGIC = b"MWCHNK01"
STATE = struct.Struct("<H18qB")
QUEUE = struct.Struct("<QQ")


def encode_state(state):
    depth, box, hint = state
    data = bytearray(STATE.pack(depth, *(v for interval in box for v in interval), len(hint)))
    for weight, labels in hint:
        data.extend(struct.pack("<QB", weight, len(labels)))
        data.extend(labels)
    result = bytes(data)
    if read_state(io.BytesIO(result)) != state:
        raise ValueError("invalid continuation state")
    return result


def read_state(stream):
    values = STATE.unpack(read_exact(stream, STATE.size))
    depth, count = values[0], values[-1]
    box = tuple(zip(values[1:19:2], values[2:19:2]))
    if depth > 256 or count > 24 or any(lo > hi for lo, hi in box):
        raise ValueError("invalid continuation domain")
    hint = []
    total = 0
    for _ in range(count):
        weight, size = struct.unpack("<QB", read_exact(stream, 9))
        if not 0 < weight <= ONE or not 3 <= size <= 13:
            raise ValueError("invalid continuation member")
        labels = tuple(read_exact(stream, size))
        if len(set(labels)) != size or any(i >= 13 for i in labels):
            raise ValueError("invalid continuation labels")
        total += weight
        hint.append((weight, labels))
    if total > ONE:
        raise ValueError("invalid continuation weights")
    return depth, box, tuple(hint)


def read_task(data):
    stream = io.BytesIO(data)
    if read_exact(stream, 8) != TASK_MAGIC:
        raise ValueError("invalid task magic")
    state = read_state(stream)
    if stream.read(1):
        raise ValueError("trailing task data")
    return state


def inspect_chunk(data, expected, stats, budget, depth_limit):
    """Check one structural tree, including every hole's exact box and depth."""
    stream = io.BytesIO(data)
    if read_exact(stream, 8) != CHUNK_MAGIC or read_state(stream) != expected:
        raise ValueError("chunk does not match its task")
    pending = [(expected[0], expected[1])]
    spans, holes = [], []
    start = stream.tell()
    nodes = leaves = 0
    reached = expected[0]
    while pending:
        depth, box = pending.pop()
        if depth > depth_limit:
            raise ValueError("chunk exceeds original depth limit")
        offset = stream.tell()
        tag = read_exact(stream, 1)[0]
        if tag == 255:
            state = read_state(stream)
            if state[:2] != (depth, box):
                raise ValueError("hole does not match its split path")
            spans.append((start, offset))
            start = stream.tell()
            holes.append(state)
            continue
        nodes += 1
        reached = max(reached, depth)
        if tag < 9:
            lo, hi = box[tag]
            mid = (lo + hi) // 2
            if depth >= depth_limit or not lo < mid < hi:
                raise ValueError("invalid continuation split")
            left, right = list(box), list(box)
            left[tag], right[tag] = (lo, mid), (mid, hi)
            pending.extend(((depth + 1, tuple(right)), (depth + 1, tuple(left))))
        else:
            leaf = read_leaf(stream, tag)
            if any(weight <= 0 for weight, _ in leaf):
                raise ValueError("invalid ordinary leaf weight")
            leaves += 1
    spans.append((start, stream.tell()))
    if stream.read(1):
        raise ValueError("trailing chunk data")
    counts = {"nodes": nodes, "leaves": leaves, "holes": len(holes), "depth": reached}
    if any(type(stats.get(k)) is not int or stats[k] != v for k, v in counts.items()):
        raise ValueError("chunk statistics do not match its tree")
    if (
        stats.get("chunk") is not True
        or stats.get("complete") is not (not holes)
        or stats.get("reason") != ("yield" if holes else "complete")
        or not 1 <= nodes <= budget
        or (holes and nodes != budget)
        or nodes + 1 != 2 * leaves + len(holes)
    ):
        raise ValueError("invalid chunk completion or budget")
    return spans, holes


def run_chunk(executable, work, task, budget, depth_limit, searches):
    source = work / f"{task}.task"
    task_bytes = source.read_bytes()
    state = read_task(task_bytes)
    output = work / f"{task}.chunk"
    log = work / f"{task}.log"
    with log.open("w") as messages:
        code = searches.run(
            [str(executable), "--chunk", str(source), str(output), str(budget), str(depth_limit)],
            messages,
        )
    if code:
        raise RuntimeError(f"native subtask {task} failed ({code}); see {log}")
    if source.read_bytes() != task_bytes:
        raise ValueError("task changed during native search")
    stats = json.loads(log.read_text().splitlines()[-1])
    data = output.read_bytes()
    spans, holes = inspect_chunk(data, state, stats, budget, depth_limit)
    return {
        "budget": budget,
        "task_sha256": hashlib.sha256(task_bytes).hexdigest(),
        "chunk_sha256": hashlib.sha256(data).hexdigest(),
        "stats": stats,
        "spans": spans,
    }, holes


def assemble(work, root_task, root_state, part, count, budget, depth_limit, destination):
    """Replace every hole exactly once in preorder, using the validated bytes."""
    visited = set()
    totals = {"nodes": 0, "leaves": 0}

    def visit(task, expected, output):
        if type(task) is not int or task < 0 or task in visited:
            raise ValueError("duplicate or cyclic continuation link")
        visited.add(task)
        record = json.loads((work / f"{task}.json").read_text())
        source = (work / f"{task}.task").read_bytes()
        data = (work / f"{task}.chunk").read_bytes()
        if (
            record["part"] != part
            or hashlib.sha256(source).hexdigest() != record["task_sha256"]
            or read_task(source) != expected
            or hashlib.sha256(data).hexdigest() != record["chunk_sha256"]
        ):
            raise ValueError("continuation bytes or ownership changed")
        chunk_budget = record["budget"]
        if type(chunk_budget) is not int or not 1 <= chunk_budget <= budget:
            raise ValueError("invalid recorded node budget")
        spans, holes = inspect_chunk(data, expected, record["stats"], chunk_budget, depth_limit)
        children = record["children"]
        if len(children) != len(holes) or [list(span) for span in spans] != record["spans"]:
            raise ValueError("continuation links do not cover every hole")
        for key in totals:
            totals[key] += record["stats"][key]
        for i, (start, end) in enumerate(spans):
            output.write(data[start:end])
            if i < len(holes):
                visit(children[i], holes[i], output)

    with destination.open("xb") as output:
        visit(root_task, root_state, output)
    if len(visited) != count or totals["nodes"] != 2 * totals["leaves"] - 1:
        raise ValueError("incomplete assembled outer tree")
    return totals


def run_frontier(executable, directory, roots, budget, depth_limit, jobs, searches):
    """Disk-backed FIFO; only at most jobs native futures reside in memory."""
    if any(type(n) is not int or n < 1 for n in (budget, jobs, depth_limit)) or depth_limit > 256:
        raise ValueError("subtask budget and jobs must be positive")
    roots = list(roots)
    if len(dict(roots)) != len(roots) or any(type(i) is not int or i < 0 for i, _ in roots):
        raise ValueError("invalid or duplicate outer part")
    progress = Progress("Lower search", len(roots), jobs)
    completed = 0
    work = Path(tempfile.mkdtemp(prefix=".subtasks-", dir=directory))
    roots = dict(roots)
    queue_path = work / "pending"
    next_task = pending = 0
    active, ready_parts = {}, []
    root_tasks, states, outstanding, task_counts, started, totals = {}, {}, {}, {}, {}, {}

    with queue_path.open("wb") as writer, queue_path.open("rb") as reader:

        def enqueue(part, state):
            nonlocal next_task, pending
            task = next_task
            next_task += 1
            (work / str(part) / f"{task}.task").write_bytes(TASK_MAGIC + encode_state(state))
            writer.write(QUEUE.pack(task, part))
            outstanding[part] = outstanding.get(part, 0) + 1
            task_counts[part] = task_counts.get(part, 0) + 1
            pending += 1
            return task

        for part, box in roots.items():
            (work / str(part)).mkdir()
            states[part] = (0, tuple((a.lo, a.hi) for a in box), ())
            root_tasks[part] = enqueue(part, states[part])
            totals[part] = {"cpu_seconds": 0.0, "depth": 0}
        pool = concurrent.futures.ThreadPoolExecutor(max_workers=jobs)
        try:
            while pending or active or ready_parts:
                progress.update(completed)
                writer.flush()
                while pending and len(active) < jobs:
                    task, part = QUEUE.unpack(read_exact(reader, QUEUE.size))
                    pending -= 1
                    chunk_budget = min(1024, budget) if pending < jobs else budget
                    started.setdefault(part, time.monotonic())
                    future = pool.submit(
                        run_chunk,
                        executable,
                        work / str(part),
                        task,
                        chunk_budget,
                        depth_limit,
                        searches,
                    )
                    active[future] = task, part
                if ready_parts:
                    part = ready_parts.pop()
                    raw = work / f"part{part:06d}.raw"
                    counts = assemble(
                        work / str(part),
                        root_tasks[part],
                        states[part],
                        part,
                        task_counts[part],
                        budget,
                        depth_limit,
                        raw,
                    )
                    if any(totals[part][key] != value for key, value in counts.items()):
                        raise ValueError("assembled counts changed")
                    stats = dict(totals[part], complete=True, reason="complete")
                    stats["cpu_seconds"] = round(stats["cpu_seconds"], 3)
                    stats["subtasks"] = task_counts[part]
                    yield part, raw, stats, round(time.monotonic() - started[part], 3)
                    # The complete raw tree now preserves this part's bytes.
                    shutil.rmtree(work / str(part))
                    completed += 1
                    continue
                finished, _ = concurrent.futures.wait(
                    active, timeout=1, return_when=concurrent.futures.FIRST_COMPLETED
                )
                # Check the whole completion batch before admitting any successors.
                results = [(future, future.result()) for future in finished]
                for future, (record, holes) in results:
                    task, part = active.pop(future)
                    record["part"] = part
                    record["children"] = [enqueue(part, state) for state in holes]
                    (work / str(part) / f"{task}.json").write_text(json.dumps(record) + "\n")
                    outstanding[part] -= 1
                    for key, value in record["stats"].items():
                        if key == "depth":
                            totals[part][key] = max(totals[part][key], value)
                        elif key == "cpu_seconds" or (type(value) is int and key not in ("holes",)):
                            totals[part][key] = totals[part].get(key, 0) + value
                    if outstanding[part] == 0:
                        ready_parts.append(part)
            if reader.read(1) or any(outstanding.values()):
                raise ValueError("unfinished continuation queue")
        except BaseException:
            searches.cancel()
            raise
        finally:
            pool.shutdown(wait=True, cancel_futures=True)
    queue_path.unlink()
    if not any(work.iterdir()):
        work.rmdir()
    progress.update(completed)
