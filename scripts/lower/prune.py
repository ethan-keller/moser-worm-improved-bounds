"""Stream ordinary pruning into a fresh, complete lower certificate."""

from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from contextlib import contextmanager
from functools import lru_cache
import ctypes
import gzip
from itertools import zip_longest
import json
from multiprocessing import get_context
from pathlib import Path
import resource
import signal
import shutil
import tempfile
import time

import checker
import chord
from certificate import encode_tree, read_leaf
from export import leaf_work
from interval import Interval, ONE
from native import Acceptor, build
from common import Progress, atomic_json, certificate_file, memory_budget, sha256_file, worker_count

POOL_LIMIT = 16
LP_MIN_LEAVES = 8
WORKER_ACCEPTOR = None
WITNESS_CACHE_LIMIT = 512
MAX_DEPTH = 256
BUFFER_SIZE = 1 << 20


class Witness:
    def __init__(self, leaf):
        self.key = tuple((weight, tuple(labels)) for weight, labels in leaf)
        chord.validate_fans(tuple(chord.Fan(*fan) for fan in self.key))
        self.leaf = [(weight, list(labels)) for weight, labels in self.key]
        self.work = leaf_work(self.leaf)
        values = [v for weight, labels in self.key for v in (weight, len(labels), *labels)]
        self.raw = (ctypes.c_int64 * len(values))(*values)


def candidate_pool(left, right):
    result, seen = [], set()
    for pair in zip_longest(left, right):
        for candidate in pair:
            if candidate is not None and candidate.key not in seen:
                result.append(candidate)
                seen.add(candidate.key)
                if len(result) == POOL_LIMIT:
                    return result
    return result


def child_boxes(box, axis):
    left, right = checker.split_box(box, axis)
    if not box[axis].lo < left[axis].hi < box[axis].hi:
        raise ValueError("certificate splits an indivisible interval")
    return left, right


def _leaf_stats(witness):
    lengths = [len(labels) for _, labels in witness.leaf]
    return dict(
        nodes=1,
        leaves=1,
        mixtures=int(len(lengths) > 1),
        depth=0,
        polygon_members=len(lengths),
        edges=sum(lengths),
        fan_rows=sum(2 * n - 5 for n in lengths if n > 5),
        work=witness.work,
    )


def _join(left, right):
    result = {key: left[key] + right[key] for key in left}
    result["nodes"] += 1
    result["depth"] = 1 + max(left["depth"], right["depth"])
    return result


def _read_node(source):
    tag = source.read(1)
    if not tag:
        raise ValueError("truncated certificate")
    return tag[0] if tag[0] < 9 else read_leaf(source, tag[0])


def prune_tree(source, output, box, acceptor, *, max_depth=MAX_DEPTH):
    """Prune into an empty seekable stream and return its final counts."""

    @lru_cache(maxsize=WITNESS_CACHE_LIMIT)
    def intern(key):
        return Witness(key)

    def witness(leaf):
        return intern(tuple((weight, tuple(labels)) for weight, labels in leaf))

    def write(data):
        if output.write(data) != len(data):
            raise OSError("short certificate write")

    def emit(whole):
        # The legacy writer canonicalizes a single full-weight mixture.
        write(encode_tree(whole.leaf))

    def visit(current, depth):
        if depth > max_depth:
            raise ValueError("certificate exceeds maximum depth")
        begin = output.tell()
        node = _read_node(source)
        if type(node) is not int:
            whole = witness(node)
            if not acceptor.prepare(current) or acceptor.check(whole) != whole.leaf:
                raise ValueError("native input contains a rejected leaf or fan anchor")
            stats = _leaf_stats(whole)
            singles = sorted(
                (witness([(ONE, labels)]) for _, labels in node), key=lambda w: (w.work, w.key)
            )
            emit(whole)
            return stats, candidate_pool([whole], singles)

        write(bytes([node]))
        lb, rb = child_boxes(current, node)
        left, pl = visit(lb, depth + 1)
        right, pr = visit(rb, depth + 1)
        pool = candidate_pool(pl, pr)
        work = left["work"] + right["work"]
        leaves = left["leaves"] + right["leaves"]
        replacement = None
        if acceptor.prepare(current):
            for proposal in sorted(pool, key=lambda w: (w.work, len(w.leaf), w.key)):
                if proposal.work >= work:
                    continue
                leaf = acceptor.check(proposal)
                if leaf is None:
                    continue
                candidate = witness(leaf)
                if candidate.work >= work:
                    continue
                replacement = candidate
                break
            if replacement is None and leaves >= LP_MIN_LEAVES:
                leaf = acceptor.mix(pool)
                if leaf is not None:
                    candidate = witness(leaf)
                    if candidate.work < work:
                        replacement = candidate
        if replacement is None:
            return _join(left, right), pool
        output.seek(begin)
        emit(replacement)
        return _leaf_stats(replacement), candidate_pool([replacement], pool)

    try:
        after, _ = visit(box, 0)
        if source.read(1):
            raise ValueError("trailing certificate data")
        # Rewrites can leave a stale suffix; discard it after consuming the whole tree.
        output.truncate()
        return after
    finally:
        intern.cache_clear()


def write_gzip(source, destination):
    """Retain the legacy gzip header/compression settings while bounding buffers."""
    with source.open("rb") as inp, destination.open("wb") as out:
        with gzip.GzipFile(
            filename="", fileobj=out, mode="wb", mtime=0, compresslevel=9
        ) as compressed:
            shutil.copyfileobj(inp, compressed, BUFFER_SIZE)


def prune_part(job):
    directory, output, part = job
    source = certificate_file(directory, part["file"])
    box = tuple(Interval(lo, hi) for lo, hi in part["box"])
    raw = Path(output) / f"part{part['id']:06d}.bin"
    destination = raw.with_suffix(".bin.gz")
    with gzip.open(source, "rb") as inp, raw.open("w+b") as out:
        counts = prune_tree(inp, out, box, WORKER_ACCEPTOR)
    write_gzip(raw, destination)
    raw.unlink()
    return {
        "id": part["id"],
        "box": part["box"],
        "path": part["path"],
        "format": 1,
        "complete": True,
        "file": destination.name,
        "sha256": sha256_file(destination),
        **counts,
    }


def worker_init(library, memory_limit):
    global WORKER_ACCEPTOR
    resource.setrlimit(resource.RLIMIT_AS, (memory_limit, memory_limit))
    WORKER_ACCEPTOR = Acceptor(library)


def load_input(directory):
    """Read a complete internal format 1 frontier; the final verifier checks it."""
    manifest = json.loads((directory / "manifest.json").read_text())
    depth = manifest["frontier_depth"]
    if (
        manifest["format"] != 1
        or manifest["complete"] is not True
        or type(depth) is not int
        or not 0 <= depth <= 16
        or sorted(p["id"] for p in manifest["parts"]) != list(range(1 << depth))
    ):
        raise ValueError("expected a complete format 1 frontier")
    return manifest


def stop_workers(pool):
    """Abort before executor shutdown; Python 3.9 has no public worker-stop API."""
    handlers = {sig: signal.signal(sig, signal.SIG_IGN) for sig in (signal.SIGINT, signal.SIGTERM)}
    try:
        # A stopped reader must not leave shutdown waiting for the queue feeder.
        queue = getattr(pool, "_call_queue", None)
        if queue is not None:
            queue.cancel_join_thread()
        workers = list((getattr(pool, "_processes", None) or {}).values())
        for worker in workers:
            if worker.is_alive():
                worker.terminate()
        deadline = time.monotonic() + 1
        for worker in workers:
            worker.join(timeout=max(0, deadline - time.monotonic()))
        for worker in workers:
            if worker.is_alive():
                worker.kill()
        deadline = time.monotonic() + 1
        for worker in workers:
            worker.join(timeout=max(0, deadline - time.monotonic()))
    finally:
        for sig, handler in handlers.items():
            signal.signal(sig, handler)


def worker_limits(requested, parts):
    if type(requested) is not int or requested < 1:
        raise ValueError("jobs must be a positive integer")
    jobs = worker_count(requested, parts, 2**30)
    memory_limit = memory_budget() // jobs
    if memory_limit < 2**30:
        raise ValueError("insufficient available memory for one pruning worker")
    return jobs, memory_limit


@contextmanager
def interruptible():
    def interrupted(signum, frame):
        raise InterruptedError("lower postprocessing interrupted")

    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, previous)


def process_parts(
    function, directory, output, parts, jobs, initializer, initargs, stage="Lower pruning"
):
    records = []
    progress = Progress(stage, len(parts), jobs)
    with ProcessPoolExecutor(
        max_workers=jobs,
        mp_context=get_context("spawn"),
        initializer=initializer,
        initargs=initargs,
    ) as pool:
        futures = []
        try:
            for part in sorted(parts, key=lambda p: p["id"]):
                futures.append(pool.submit(function, (directory, output, part)))
            pending = set(futures)
            while pending:
                finished, pending = wait(pending, timeout=1, return_when=FIRST_COMPLETED)
                for future in finished:
                    records.append(future.result())
                progress.update(len(records))
        except BaseException:
            for future in futures:
                future.cancel()
            stop_workers(pool)
            raise
    return sorted(records, key=lambda p: p["id"])


def collect_parts(output, work, upstream, records, version):
    for record in records:
        (work / record["file"]).replace(output / record["file"])
    metadata = {
        "format": version,
        "complete": True,
        "frontier_depth": upstream["frontier_depth"],
        "parts": records,
    }
    if version == 2:
        metadata["encoding"] = chord.LOWER_CHORD_ENCODING
    return metadata


def run(input: Path, output: Path, jobs: int):
    input, output = Path(input).resolve(), Path(output).resolve()
    if input == output or input in output.parents or output in input.parents:
        raise ValueError("input and output directories must be disjoint")
    upstream = load_input(input)
    jobs, memory_limit = worker_limits(jobs, len(upstream["parts"]))
    output.mkdir(parents=True)
    with interruptible(), tempfile.TemporaryDirectory(dir=output, prefix=".prune-") as temporary:
        work = Path(temporary)
        library = build(work, "accept")
        records = process_parts(
            prune_part, input, work, upstream["parts"], jobs, worker_init, (library, memory_limit)
        )
        metadata = collect_parts(output, work, upstream, records, 1)
    atomic_json(output / "manifest.json", metadata)
    return metadata
