#!/usr/bin/env python3
"""Compare original and logged checker verdicts AND reasons on an entire corpus.

Run under the host's heavy/taskset wrapper. Example:
  python3 oracle/tools/check_logged.py CORPUS --mode d3 --jobs 8 --save OUT

Every claim.bin with a sibling witness.bin below CORPUS is checked, including
out-of-domain cases. Nonzero exits, malformed output, duplicate/unknown cases,
and missing results fail the run. Saved JSONL is also accepted by difftest_d3.py
as --lean-from, so the logged results can be compared with nearcore and Python.
Timings are diagnostic wall times under concurrency, not scoring measurements.
--original-from reuses a complete original-checker JSONL baseline; its case paths
must match CORPUS exactly. The report records the baseline's digest and provenance.
"""

import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import time


DEFAULT_CHECKER = Path(__file__).resolve().parents[1] / "wasm-d3/lean/.lake/build/bin/nearspec-v3-check-logged"


def parse_results(stdout, cases):
    expected = set(cases)
    results = {}
    for line in stdout.splitlines():
        row = json.loads(line)
        case = row["case"]
        if case not in expected or case in results:
            raise ValueError(f"unknown or duplicate case: {case}")
        if row["verdict"] not in {"accept", "reject", "out_of_domain"}:
            raise ValueError(f"invalid verdict for {case}")
        if not isinstance(row["reason"], str):
            raise ValueError(f"invalid reason for {case}")
        results[case] = row
    missing = expected - results.keys()
    if missing:
        raise ValueError(f"missing {len(missing)} results; first: {min(missing)}")
    return results


def run_batch(checker, mode, cases):
    process = subprocess.run(
        [str(checker), f"--{mode}", *cases],
        capture_output=True, text=True, check=True,
    )
    return parse_results(process.stdout, cases)


def run(checker, mode, cases, jobs, batch_size):
    batches = [cases[i:i + batch_size] for i in range(0, len(cases), batch_size)]
    results = {}
    start = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for batch in pool.map(lambda dirs: run_batch(checker, mode, dirs), batches):
            results.update(batch)
    return results, time.monotonic() - start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("--checker", type=Path, default=DEFAULT_CHECKER)
    parser.add_argument("--mode", choices=("d2", "d3"), required=True)
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--batch-size", type=int, default=100)
    parser.add_argument("--save", type=Path, required=True)
    parser.add_argument("--original-from", type=Path)
    args = parser.parse_args()
    if args.jobs < 1 or args.batch_size < 1:
        parser.error("jobs and batch-size must be positive")
    cases = sorted(str(p.parent) for p in args.corpus.resolve().rglob("claim.bin"))
    if not cases:
        parser.error("corpus contains no claim.bin files")
    missing = [case for case in cases if not (Path(case) / "witness.bin").is_file()]
    if missing:
        parser.error(f"missing witness.bin: {missing[0]}")
    # Refuse to overwrite evidence from an earlier run, especially a failed run.
    args.save.mkdir(parents=True, exist_ok=False)
    summary = {
        "corpus": str(args.corpus.resolve()), "checker": str(args.checker.resolve()),
        "mode": args.mode, "cases": len(cases), "jobs": args.jobs,
        "batch_size": args.batch_size, "status": "running", "seconds": {},
    }
    summary_path = args.save / "summary.json"

    def save_summary():
        summary_path.write_text(json.dumps(summary, indent=2) + "\n")

    save_summary()
    outputs = {}
    try:
        for label, mode in (("original", args.mode), ("logged", args.mode + "l")):
            if label == "original" and args.original_from:
                baseline = args.original_from.read_bytes()
                rows = parse_results(baseline.decode(), cases)
                seconds = None
                summary["original_from"] = {
                    "path": str(args.original_from.resolve()),
                    "sha256": hashlib.sha256(baseline).hexdigest(),
                }
                print(f"original: loaded all {len(cases)} baseline results", flush=True)
            else:
                print(f"{label}: checking {len(cases)} cases", flush=True)
                rows, seconds = run(args.checker.resolve(), mode, cases, args.jobs, args.batch_size)
            outputs[label] = rows
            summary["seconds"][label] = seconds
            with (args.save / f"{label}.jsonl").open("w") as stream:
                for case in cases:
                    stream.write(json.dumps(rows[case]) + "\n")
            save_summary()
        differences = [
            {"case": case, "original": outputs["original"][case], "logged": outputs["logged"][case]}
            for case in cases
            if any(outputs["original"][case][key] != outputs["logged"][case][key]
                   for key in ("verdict", "reason"))
        ]
        (args.save / "differences.json").write_text(json.dumps(differences, indent=2) + "\n")
        summary["differences"] = len(differences)
        summary["status"] = "pass" if not differences else "fail"
    except Exception as error:
        summary["status"] = "error"
        summary["error"] = str(error)
        if isinstance(error, subprocess.CalledProcessError):
            summary["stderr"] = error.stderr[-4000:]
        save_summary()
        raise
    save_summary()
    print(json.dumps(summary, indent=2), flush=True)
    return 0 if summary["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
