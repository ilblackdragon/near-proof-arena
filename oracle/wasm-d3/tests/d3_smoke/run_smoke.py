#!/usr/bin/env python3
"""Exercise the D3 drivers and the difftest comparison contract against the committed smoke fixture.

This is the CI-runnable check for W01's "required successor modules and drivers are actually built by
CI; CI definitions are exercised, not accepted solely because YAML contains a command" criterion. It
does not need the 8.5 GiB corpora: the seven cases under `cases/` are committed real D3 cases.

What it asserts:

  1. Every driver binary exists and exits 0 on every fixture case, emitting one JSON verdict line per
     case in the documented format. A missing binary or a crash is a failure.
  2. Every driver is compared against **its own** declared expectation domain, using the difftest
     comparison contract (`difftest_d3.compare`): the baseline driver as `domain=baseline`, and each
     widening driver as `domain=successor` with the exclusion family that driver lifts. A driver that
     stops widening, widens wrongly, or returns a wrong accept/reject fails its own comparison. This
     replaces the earlier check that only compared the baseline and merely *ran* the other three.
  3. Each widening driver decides the cases its tier widens: the case the baseline excludes for
     `c.not_genesis` / `e.float` / `e.g_alpha` must come back `accept` from the driver that lifts
     that family — the successor/baseline expectation split, measured per driver.
  4. A deliberately wrong verdict fails the comparison for every driver, not just the baseline.

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

# Each driver's own expectation domain. `domain="baseline"` expects an exclusion exactly on the
# oracle's out-of-domain cases; `domain="successor"` with `widen` moves the cases whose violations are
# a subset of `widen` into the driver's domain and expects a nearcore-matching verdict there. The
# widen sets are the tiers these binaries implement (`checkD3F` = floats, `checkD3G` = genesis,
# `checkD3Proto` = protocol-gas band); see spec/lean/v3/MainD3G.lean and MainD3Proto.lean.
DRIVERS = {
    "baseline": {
        "path": REPO / "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3",
        "domain": "baseline",
        "widen": (),
        "note": "checkD3 (D3alpha)",
    },
    "float": {
        "path": REPO / "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3f",
        "domain": "successor",
        "widen": ("e.float",),
        "note": "checkD3F (float types/operators)",
    },
    "genesis": {
        "path": REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3g",
        "domain": "successor",
        "widen": ("c.not_genesis",),
        "note": "checkD3G (genesis chunks)",
    },
    "proto": {
        "path": REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-d3proto",
        "domain": "successor",
        "widen": ("e.g_alpha",),
        "note": "checkD3Proto (protocol-gas band)",
    },
}

# Cases each widening driver must decide, and the verdict it must give. The baseline must exclude
# every one of them; that is what makes these a measured widening rather than a restatement.
MUST_WIDEN = {
    "float": [("d3c9-ood-00-h10072-s3", "e.float", "accept")],
    "genesis": [("d3c7-ood-00-h10002-s0", "c.not_genesis", "accept")],
    "proto": [("d3c7-ood-00-h10007-s1", "e.g_alpha", "accept")],
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
    return load_compare().parse_results(proc.stdout.splitlines(), [str(c) for c in cases])


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

    bins = {}
    for name, spec in DRIVERS.items():
        path = Path(spec["path"])
        if a.bin_dir:
            path = Path(a.bin_dir) / path.name
        if not path.is_file():
            raise SystemExit(f"FAIL: {name} driver missing: {path} "
                             f"(build it: see docs/logs/lean-chunk-L7-2026-10-24.md §4)")
        bins[name] = path

    dirs = [os.path.normpath(str(c)) for c in cases]
    results = {name: run(path, cases) for name, path in bins.items()}
    summary = {"schema": "near-d3-smoke-result-v2", "cases": len(cases), "drivers": {}}
    d3 = load_compare()

    # 1 + 2: every driver ran, and every driver matches its own declared expectation domain.
    for name, got in results.items():
        spec = DRIVERS[name]
        summary["drivers"][name] = {
            "binary": str(bins[name]),
            "note": spec["note"],
            "domain": spec["domain"],
            "widen": list(spec["widen"]),
            "verdicts": {k: sum(1 for d in dirs if got[d]["verdict"] == k)
                         for k in ("accept", "reject", "out_of_domain")},
        }
        _, bad, partition, _ = d3.compare(name, dirs, metas, got,
                                         domain=spec["domain"], widen=spec["widen"])
        summary["drivers"][name]["partition"] = dict(sorted(partition.items()))
        if bad:
            for b in bad:
                print(f"DISAGREE ({name})", *b, sep="\n  ")
            raise SystemExit(f"FAIL: {name} driver has {len(bad)} disagreement(s) against its own "
                             f"domain {spec['domain']} widen={spec['widen']}")
        if sum(partition.values()) != len(dirs):
            raise SystemExit(f"FAIL: {name} partition covers {sum(partition.values())} "
                             f"of {len(dirs)}")

    # 3: each widening driver decides the family its tier lifts; the baseline excludes those cases.
    summary["successor_widening"] = []
    for name, wanted in MUST_WIDEN.items():
        for case_dir, family, expected in wanted:
            d = os.path.normpath(str(FIXTURE / case_dir))
            if d not in metas:
                raise SystemExit(f"FAIL: widening case {case_dir} missing from the fixture")
            base_v = results["baseline"][d]["verdict"]
            got_v = results[name][d]["verdict"]
            if base_v != "out_of_domain":
                raise SystemExit(f"FAIL: baseline did not exclude {case_dir} (got {base_v})")
            if got_v != expected:
                raise SystemExit(f"FAIL: {name} did not {expected} {case_dir} (got {got_v})")
            summary["successor_widening"].append(
                {"case": case_dir, "driver": name, "widens": family,
                 "baseline": base_v, "driver_verdict": got_v,
                 "d3_violations": metas[d].get("d3_violations")})
    # Every widening family the fixture claims must be exercised by at least one driver.
    covered = {w["widens"] for w in summary["successor_widening"]}
    if covered != {"c.not_genesis", "e.float", "e.g_alpha"}:
        raise SystemExit(f"FAIL: fixture does not exercise every widening family: {sorted(covered)}")

    # 4: the controlled-breakage control, per driver. One flipped verdict must make compare() fail.
    summary["controlled_breakage"] = []
    for name, got in results.items():
        spec = DRIVERS[name]
        broken = {d: dict(got[d]) for d in dirs}
        target = next(d for d in dirs if broken[d]["verdict"] == "accept")
        broken[target]["verdict"] = "reject"
        _, broken_bad, _, _ = d3.compare(name, dirs, metas, broken,
                                        domain=spec["domain"], widen=spec["widen"])
        if not broken_bad:
            raise SystemExit(f"FAIL: controlled breakage did not fail {name} "
                             f"({os.path.basename(target)})")
        summary["controlled_breakage"].append(
            {"driver": name, "case": os.path.basename(target), "flipped_to": "reject",
             "disagreements": len(broken_bad)})

    print(f"smoke: {len(cases)} cases, {len(bins)} drivers built and run")
    for name, d in summary["drivers"].items():
        print(f"  {name:9s} domain={d['domain']:9s} widen={','.join(d['widen']) or '-':14s} "
              f"{d['verdicts']} partition={json.dumps(d['partition'], sort_keys=True)}")
    for w in summary["successor_widening"]:
        print(f"  widening: {w['driver']} lifts {w['widens']} on {w['case']} "
              f"({w['baseline']} -> {w['driver_verdict']})")
    print(f"  controlled breakage: "
          f"{sum(c['disagreements'] for c in summary['controlled_breakage'])} disagreement(s) "
          f"from flipping one verdict per driver ({len(summary['controlled_breakage'])} drivers)")
    if a.report:
        with open(a.report, "w") as f:
            json.dump(summary, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"  wrote {a.report}")
    print("SMOKE PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
