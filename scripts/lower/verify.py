#!/usr/bin/env python3
"""Export a complete lower certificate and check every proof in the Lean kernel."""

import argparse
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, build_modules, directory_lock, run, source_snapshot, worker_count
from certificate import inputs
from export import export
from pack import pack_generated

LEAF_LIMIT = 256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", type=Path, default=ROOT / "certificates/lower")
    parser.add_argument("--jobs", type=int, help="maximum workers; default fits CPUs and memory")
    args = parser.parse_args()
    # Allow 1.5 GiB per worker, with separate headroom for memory peaks.
    jobs = worker_count(args.jobs, 50, 3 * 2**29)
    certificates = args.certificates.resolve()
    ns = "MoserWorm.LowerBound.Certificate"
    directory = (ROOT / "MoserWorm/LowerBound/Certificate/Generated").resolve()
    if certificates.is_relative_to(directory) or directory.is_relative_to(certificates):
        parser.error("certificate and generated-source directories must be disjoint")
    logs = ROOT / ".lake/logs/lower"
    with directory_lock(certificates), directory_lock(directory):
        print(f"Lower verification: checking certificate files; logs: {logs}", flush=True)
        sources = source_snapshot()
        before = inputs(certificates)[0]
        run(
            "soundness",
            ["lake", "build", ns + ".Complete", ns + ".Chord.Sound"],
            logs,
        )
        print("Lower verification: exporting Lean proofs...", flush=True)
        manifest = export(certificates, directory, LEAF_LIMIT)
        print("Lower verification: packing Lean proofs...", flush=True)
        manifest = pack_generated(directory, manifest)
        build_modules(manifest["modules"], jobs, logs)
        run("theorem", ["lake", "--rehash", "build", "MoserWorm.LowerBound.Main"], logs)
        if source_snapshot() != sources:
            raise ValueError("sources changed during verification")
        if inputs(certificates)[0] != before:
            raise ValueError("lower certificates changed during verification")
    print(f"Lower bound checked. Logs: {logs}")


if __name__ == "__main__":
    main()
