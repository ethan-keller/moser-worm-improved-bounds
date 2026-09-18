#!/usr/bin/env python3
"""Generate a portable upper certificate from the fixed header by conic search."""

import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from contextlib import redirect_stderr, redirect_stdout
import gzip
import importlib.metadata
import json
from multiprocessing import get_context
import os
from pathlib import Path
import resource
import signal
import sys
import time
import traceback

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, atomic_json, sha256_file, worker_count

WORKER = None
MEMORY_PER_WORKER = 4 * 2**30
MAX_SECONDS = 4 * 60 * 60
MAX_DEPTH = 128


def worker_init(header, logs):
    global WORKER
    sys.stdout = sys.stderr = (logs / f"worker-{os.getpid()}.log").open("w", buffering=1)
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_PER_WORKER, MEMORY_PER_WORKER))
    from search_model import Model

    WORKER = Model(header)


def worker_expand(state):
    return WORKER.expand(state)


def stop_workers(pool):
    queue = getattr(pool, "_call_queue", None)
    if queue is not None:
        queue.cancel_join_thread()
    workers = list((getattr(pool, "_processes", None) or {}).values())
    for worker in workers:
        if worker.is_alive():
            worker.terminate()
    for worker in workers:
        worker.join(timeout=1)
        if worker.is_alive():
            worker.kill()
    for worker in workers:
        worker.join(timeout=1)
    pool.shutdown(wait=True, cancel_futures=True)


def install(nodes, index, decision):
    depth = nodes[index][2]

    def child(state):
        i = len(nodes)
        nodes.append(["pending", state, depth + 1])
        return i

    start = len(nodes)
    if decision[0] == "p":
        nodes[index] = ["p", decision[1], child(decision[2]), child(decision[3])]
    elif decision[0] == "s":
        nodes[index] = ["s", [[rect, child(state)] for rect, state in decision[1]]]
    elif decision[0] in ("l", "unresolved"):
        nodes[index] = decision
    else:
        raise ValueError("invalid worker decision")
    return range(start, len(nodes))


def search(header, jobs, logs, console=None):
    started = time.monotonic()
    for name in (
        "OPENBLAS_NUM_THREADS",
        "OMP_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
    ):
        os.environ[name] = "1"
    for line in (ROOT / "requirements-upper-search.txt").read_text().splitlines():
        if line and not line.startswith("#"):
            name, expected = line.split("==")
            actual = importlib.metadata.version(name)
            if actual != expected:
                raise ValueError(f"{name}: expected {expected}, found {actual}")
    nodes = [["pending", [[], [0, header["kR"], 0, header["kL"]], [], []], 0]]
    pending, running = deque([0]), {}
    expanded = unresolved = 0
    last_report = started
    pool = ProcessPoolExecutor(
        max_workers=jobs,
        mp_context=get_context("spawn"),
        initializer=worker_init,
        initargs=(header, logs),
    )
    old_handlers = {}

    def interrupt(signum, frame):
        raise InterruptedError(f"signal {signum}")

    try:
        for sig in (signal.SIGTERM, signal.SIGINT):
            old_handlers[sig] = signal.signal(sig, interrupt)
        while pending or running:
            remaining = MAX_SECONDS - (time.monotonic() - started)
            if remaining <= 0:
                raise TimeoutError("upper search exceeded its four-hour limit")
            while pending and len(running) < jobs:
                i = pending.popleft()
                if nodes[i][2] > MAX_DEPTH:
                    nodes[i] = ["unresolved", "depth limit"]
                    unresolved += 1
                    continue
                running[pool.submit(worker_expand, nodes[i][1])] = i
            if not running:
                break
            ready, _ = wait(running, timeout=min(1, remaining), return_when=FIRST_COMPLETED)
            for future in sorted(ready, key=lambda f: running[f]):
                i = running.pop(future)
                decision = future.result()
                pending.extend(install(nodes, i, decision))
                expanded += 1
                unresolved += decision[0] == "unresolved"
            if time.monotonic() - last_report >= 60:
                print(
                    f"Upper search: {expanded} nodes explored; {len(pending)} queued; "
                    f"{len(running)} running; {unresolved} unresolved; "
                    f"{(time.monotonic() - started) / 60:.1f} min elapsed.",
                    file=console,
                    flush=True,
                )
                last_report = time.monotonic()
        if time.monotonic() - started >= MAX_SECONDS:
            raise TimeoutError("upper search exceeded its four-hour limit")
    except BaseException:
        stop_workers(pool)
        raise
    else:
        pool.shutdown(wait=True, cancel_futures=True)
    finally:
        for sig, handler in old_handlers.items():
            signal.signal(sig, handler)
    if unresolved:
        raise RuntimeError(f"upper search left {unresolved} unresolved nodes")
    print(
        f"Upper search complete: {expanded} nodes in {time.monotonic() - started:.1f}s",
        file=console,
        flush=True,
    )
    return nodes


def write_gzip(path, value, *, lines=False):
    with path.open("wb") as raw:
        with gzip.GzipFile(fileobj=raw, mode="wb", filename="", mtime=0) as stream:
            values = value if lines else [value]
            for item in values:
                stream.write((json.dumps(item, separators=(",", ":")) + "\n").encode("ascii"))


def write_certificate(directory, header, nodes):
    leaves = []

    def visit(index):
        node = nodes[index]
        if node[0] == "l":
            i = len(leaves)
            leaves.append([i, node[1], node[2]])
            return ["l", i]
        if node[0] == "p":
            return ["p", node[1], visit(node[2]), visit(node[3])]
        if node[0] == "s":
            return ["s", [[rect, visit(child)] for rect, child in node[1]]]
        raise ValueError("cannot publish an incomplete tree")

    tree = visit(0)
    if not leaves:
        raise ValueError("empty certificate")
    directory.mkdir()
    atomic_json(directory / "header.json", {**header, "leaves": len(leaves), "complete": True})
    write_gzip(directory / "tree.json.gz", tree)
    files = []
    for offset in range(0, len(leaves), 256):
        name = f"multipliers-{offset // 256:03d}.jsonl.gz"
        write_gzip(directory / name, leaves[offset : offset + 256], lines=True)
        files.append(name)
    atomic_json(
        directory / "manifest.json",
        {
            "schema": 1,
            "files": files,
            "normalized_rows": sum(len(x[2]) for x in leaves),
            "sha256": {
                name: sha256_file(directory / name)
                for name in ["header.json", "tree.json.gz", *files]
            },
        },
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "build/certificates/upper")
    parser.add_argument(
        "--jobs", type=int, default=None, help="maximum workers (default: auto; cap: 16)"
    )
    args = parser.parse_args()
    if args.jobs is not None and args.jobs < 1:
        parser.error("jobs must be positive")
    output = args.output.absolute()
    work = output.with_name(output.name + "-work")
    if any(path.exists() or path.is_symlink() for path in (output, work)):
        parser.error("output and work directories must both be new")
    jobs = worker_count(args.jobs, 16, MEMORY_PER_WORKER, reserve=4 * 2**30)
    work.mkdir(parents=True)
    logs = work / "logs"
    logs.mkdir()
    print(f"Upper search: {jobs} workers; logs: {logs}", flush=True)
    console = sys.stdout
    with (logs / "generate.log").open("w", buffering=1) as log:
        with redirect_stdout(log), redirect_stderr(log):
            try:
                header = json.loads((ROOT / "certificates/upper/header.json").read_text())
                nodes = search(header, jobs, logs, console)
                payload = work / "certificate"
                print(
                    "Upper certificate: compressing and publishing files...",
                    file=console,
                    flush=True,
                )
                write_certificate(payload, header, nodes)
                if output.exists() or output.is_symlink():
                    raise FileExistsError(f"output appeared during generation: {output}")
                payload.rename(output)
            except BaseException:
                traceback.print_exc()
                raise
    print(f"Upper certificate generated: {output}. Logs: {logs}")


if __name__ == "__main__":
    main()
