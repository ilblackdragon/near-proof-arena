#!/usr/bin/env python3
"""Exercise the D3 drivers and the difftest comparison contract against the committed smoke fixture.

This is the CI-runnable check for W01's "required successor modules and drivers are actually built by
CI; CI definitions are exercised, not accepted solely because YAML contains a command" criterion. It
does not need the 8.5 GiB corpora: the five cases under `cases/` are committed real D3 cases.

What it asserts:

  1. Every driver binary exists and exits 0 on every fixture case, emitting one JSON verdict line per
     case in the documented format. A missing binary or a crash is a failure.
  2. The baseline driver `nearspec-v3-check-d3` produces the oracle's baseline expectation for each
     case: accept/reject where `in_d3`, and an *asserted* out-of-domain exclusion where not.
  3. The genesis driver `nearspec-v3-check-d3g` accepts the `c.not_genesis` case that the baseline
     excludes — the successor/baseline expectation split, measured rather than asserted.
  4. `difftest_d3.compare()` partitions every case exactly once and reports zero disagreements, and a
     deliberately wrong verdict makes it fail (the controlled-breakage control).

Exit 0 only if all four hold. Usage:

  python3 oracle/wasm-d3/tests/d3_smoke/run_smoke.py [--bin-dir DIR]
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
FIXTURE = HERE / "cases"
DEFAULT_BIN = {
    "baseline": REPO / "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3",
    "float": REPO / "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3f",
    "genesis": REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3g",
    "proto": REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3proto",
}


def load_compare():
    spec = importlib.util.spec_from_file_location(
        "difftest_d3_smoke", REPO / "oracle/v3-d3/tools/difftest_d3.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def run(binary, cases):
    proc = subprocess.run([str(binary)] + [str(c) for c in cases],
                          capture_output=True, text=True, timeout=600)
    if proc.returncode != 0:
        raise SystemExit(f"FAIL: {binary.name} exited {proc.returncode}\n{proc.stderr[:2000]}")
    got = {}
    for line in proc.stdout.splitlines():
        if not line.startswith("{"):
            continue
        row = json.loads(line)
        got[os.path.normpath(row["case"])] = row
    missing = [str(c) for c in cases if os.path.normpath(str(c)) not in got]
    if missing:
        raise SystemExit(f"FAIL: {binary.name} produced no verdict for {missing[:3]}"
                         f" ({len(missing)} missing)")
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin-dir", default=None, help="directory holding the four driver binaries")
    ap.add_argument("--report", default=None, help="write a JSON summary here")
    a = ap.parse_args()

    index = json.load(open(FIXTURE / "index.json"))
    entries = index["cases"]
    cases = [FIXTURE / e["case_dir"] for e in entries]
    metas = {}
    for e, c in zip(entries, cases):
        m = json.load(open(c / "meta.json"))
        metas[os.path.normpath(str(c))] = m

    bins = dict(DEFAULT_BIN)
    if a.bin_dir:
        for k in bins:
            bins[k] = Path(a.bin_dir) / bins[k].name
    for name, path in bins.items():
        if not Path(path).is_file():
            raise SystemExit(f"FAIL: {name} driver missing: {path} "
                             f"(build it: see docs/logs/lean-chunk-L7-2026-10-24.md §4)")

    dirs = [os.path.normpath(str(c)) for c in cases]
    results = {name: run(path, cases) for name, path in bins.items()}
    summary = {"schema": "near-d3-smoke-result-v1", "cases": len(cases), "drivers": {}}

    # 1 + 2: every driver ran; the baseline matches the oracle's baseline expectation.
    d3 = load_compare()
    for name, got in results.items():
        summary["drivers"][name] = {
            "binary": str(bins[name]),
            "verdicts": {k: sum(1 for d in dirs if got[d]["verdict"] == k)
                         for k in ("accept", "reject", "out_of_domain")},
        }

    _, bad, partition, records = d3.compare("baseline", dirs, metas, results["baseline"])
    if bad:
        for b in bad:
            print("DISAGREE", *b, sep="\n  ")
        raise SystemExit(f"FAIL: baseline driver has {len(bad)} disagreement(s) on the smoke fixture")
    if sum(partition.values()) != len(dirs):
        raise SystemExit(f"FAIL: partition covers {sum(partition.values())} of {len(dirs)}")
    summary["baseline_partition"] = dict(sorted(partition.items()))
    summary["baseline_records"] = records

    # 3: the genesis driver accepts the c.not_genesis case the baseline excludes.
    genesis_only = [d for d in dirs if "c.not_genesis" in (metas[d].get("d3_violations") or [])]
    if not genesis_only:
        raise SystemExit("FAIL: smoke fixture has no c.not_genesis case")
    for d in genesis_only:
        base_v = results["baseline"][d]["verdict"]
        gen_v = results["genesis"][d]["verdict"]
        if base_v != "out_of_domain":
            raise SystemExit(f"FAIL: baseline did not exclude {os.path.basename(d)} (got {base_v})")
        if gen_v != "accept":
            raise SystemExit(f"FAIL: genesis driver did not accept {os.path.basename(d)} (got {gen_v})")
        summary.setdefault("successor_widening", []).append(
            {"case": os.path.basename(d), "baseline": base_v, "genesis": gen_v,
             "d3_violations": metas[d].get("d3_violations")})

    # 4: the controlled-breakage control. One flipped verdict must make compare() fail.
    broken = {d: dict(results["baseline"][d]) for d in dirs}
    target = next(d for d in dirs if results["baseline"][d]["verdict"] == "accept")
    broken[target]["verdict"] = "reject"
    _, broken_bad, broken_part, _ = d3.compare("baseline", dirs, metas, broken)
    if not broken_bad:
        raise SystemExit(f"FAIL: controlled breakage did not fail ({os.path.basename(target)})")
    summary["controlled_breakage"] = {
        "case": os.path.basename(target), "flipped_to": "reject",
        "disagreements": len(broken_bad),
        "partition": dict(sorted(broken_part.items())),
    }

    print(f"smoke: {len(cases)} cases, 4 drivers built and run, baseline partition "
          f"{json.dumps(summary['baseline_partition'], sort_keys=True)}")
    for name, d in summary["drivers"].items():
        print(f"  {name:9s} {d['verdicts']}")
    print(f"  successor widening: {summary['successor_widening']}")
    print(f"  controlled breakage: {summary['controlled_breakage']['disagreements']} disagreement(s) "
          f"from flipping {summary['controlled_breakage']['case']}")
    if a.report:
        with open(a.report, "w") as f:
            json.dump(summary, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"  wrote {a.report}")
    print("SMOKE PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
