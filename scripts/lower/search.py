"""Run the fixed native lower search and assemble complete certificates."""

from contextlib import closing
import gzip
import os
from pathlib import Path
import subprocess
import signal
import shutil
import threading
import time

import checker
from subtasks import run_frontier

from common import atomic_json, atomic_text, directory_lock, sha256_file, worker_count

SOURCE = Path(__file__).with_name("search.c")
FRONTIER_DEPTH = 10
MAX_DEPTH = 160
SUBTASK_NODES = 4096


def _build_search(directory):
    directory.mkdir()
    atomic_text(directory / "data.h", checker.c_header())
    executable = directory / "search"
    subprocess.run(
        [
            "gcc",
            "-O3",
            "-std=c11",
            "-ffp-contract=off",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-I",
            str(directory),
            str(SOURCE),
            "-lm",
            "-o",
            str(executable),
        ],
        check=True,
    )
    return executable


def frontier(depth):
    boxes = [(checker.root_box(), [])]
    for _ in range(depth):
        next_boxes = []
        for box, path in boxes:
            axis = checker.split_axis(box)
            left, right = checker.split_box(box, axis)
            next_boxes.extend(((left, path + [(axis, False)]), (right, path + [(axis, True)])))
        boxes = next_boxes
    return boxes


class Searches:
    """Own search process groups so interruption does not leave native jobs running."""

    def __init__(self):
        self.lock = threading.Lock()
        self.processes = set()
        self.cancelled = False

    def run(self, command, output):
        process = None
        try:
            with self.lock:
                if self.cancelled:
                    raise RuntimeError("search cancelled")
                process = subprocess.Popen(
                    command, stdout=output, stderr=subprocess.STDOUT, start_new_session=True
                )
                self.processes.add(process)
            return process.wait()
        except BaseException:
            # Unwind wait() before cancellation; a signal handler must only raise,
            # not reenter subprocess's non-reentrant waitpid lock.
            self.cancel()
            raise
        finally:
            if process is not None:
                with self.lock:
                    self.processes.discard(process)

    def cancel(self):
        previous = signal.pthread_sigmask(
            signal.SIG_BLOCK, (signal.SIGINT, signal.SIGTERM, signal.SIGALRM)
        )
        try:
            self._cancel()
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous)

    def _cancel(self):
        with self.lock:
            self.cancelled = True
            processes = list(self.processes)
        for process in processes:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + 2
        for process in processes:
            try:
                process.wait(timeout=max(0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
        for process in processes:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


def publish_tree(directory, index, box, path, raw_file, stats, seconds):
    if stats.get("complete") is not True:
        raise ValueError("search did not report completion")
    destination = directory / f"part{index:06d}.bin.gz"
    temporary = destination.with_suffix(".gz.partial")
    with raw_file.open("rb") as source:
        with temporary.open("wb") as out:
            with gzip.GzipFile(
                filename="", fileobj=out, mode="wb", mtime=0, compresslevel=9
            ) as data:
                shutil.copyfileobj(source, data, 1024 * 1024)
    temporary.replace(destination)
    record = {
        "id": index,
        "path": path,
        "box": [[a.lo, a.hi] for a in box],
        "seconds": seconds,
        **stats,
        "file": destination.name,
        "sha256": sha256_file(destination),
    }
    raw_file.unlink()
    return record


def run(output: Path, jobs: int):
    """Search the entire fixed frontier in a new directory; return its manifest."""
    jobs = worker_count(jobs, 64, 256 * 2**20)
    output = Path(output).absolute()
    with directory_lock(output):
        output.mkdir(parents=True)
        executable = _build_search(output / "work")
        boxes = frontier(FRONTIER_DEPTH)
        metadata = {
            "format": 1,
            "complete": False,
            "frontier_depth": FRONTIER_DEPTH,
            "parts": [],
        }
        manifest_path = output / "manifest.json"
        atomic_json(manifest_path, metadata)
        records = {}
        searches = Searches()
        old_sigterm = None
        if threading.current_thread() is threading.main_thread():

            def terminated(signum, frame):
                raise InterruptedError("generation terminated")

            old_sigterm = signal.signal(signal.SIGTERM, terminated)
        try:
            with closing(
                run_frontier(
                    executable,
                    output,
                    [(i, box) for i, (box, _) in enumerate(boxes)],
                    SUBTASK_NODES,
                    MAX_DEPTH,
                    jobs,
                    searches,
                )
            ) as chunks:
                for i, raw, stats, seconds in chunks:
                    if type(i) is not int or not 0 <= i < len(boxes) or i in records:
                        raise ValueError("invalid or duplicate frontier id")
                    records[i] = publish_tree(output, i, *boxes[i], raw, stats, seconds)
        except BaseException:
            searches.cancel()
            raise
        finally:
            if old_sigterm is not None:
                signal.signal(signal.SIGTERM, old_sigterm)
        if set(records) != set(range(len(boxes))):
            raise ValueError("search output does not cover its complete frontier")
        metadata["parts"] = [records[i] for i in sorted(records)]
        metadata["complete"] = True
        atomic_json(manifest_path, metadata)
        return metadata
