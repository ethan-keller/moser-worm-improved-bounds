#!/usr/bin/env python3
"""Generate a fresh, compressed lower certificate for separate Lean verification."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, directory_lock, worker_count


def run(output: Path, jobs: int):
    """Run native search, ordinary pruning, chord pruning, and publication."""
    import search
    import prune
    import chord_prune

    if type(jobs) is not int or jobs < 1:
        raise ValueError("jobs must be a positive integer")
    output = Path(output).absolute()
    work = output.with_name(output.name + "-work")
    with directory_lock(output):
        if output.exists() or output.is_symlink() or work.exists() or work.is_symlink():
            raise ValueError("choose new output and work directories")
        work.mkdir(parents=True)
        print(f"Lower search: preparing native workers; work: {work}", flush=True)
        search.run(work / "raw", jobs)
        print("Lower pruning: preparing workers...", flush=True)
        prune.run(work / "raw", work / "pruned", worker_count(jobs, 32, 2**30))
        print("Lower chord pruning: preparing workers...", flush=True)
        metadata = chord_prune.run(work / "pruned", work / "lower", worker_count(jobs, 32, 2**30))
        print("Lower certificate: publishing compressed files...", flush=True)
        if output.exists() or output.is_symlink():
            raise ValueError("output directory already exists")
        (work / "lower").rename(output)
        return metadata


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "build/certificates/lower")
    parser.add_argument(
        "--jobs", type=int, default=None, help="maximum workers (default: automatic, up to 64)"
    )
    args = parser.parse_args()
    if args.jobs is not None and args.jobs < 1:
        parser.error("jobs must be positive")
    run(args.output, worker_count(args.jobs, 64))
    print(f"Lower certificate generated in {args.output}.")


if __name__ == "__main__":
    main()
