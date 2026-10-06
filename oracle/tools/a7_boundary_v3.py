#!/usr/bin/env python3
"""A7 (`w.unfolded`) boundary conformance for domain D0a.

For every case that is in D0a at the challenge bound B0, with U = unfold_bytes (Lean), both
checkers are run at bound U (must accept: just in domain) and at bound U - 1 (must report
out_of_domain with w.unfolded: just out of domain). This exercises the exact comparison
`unfoldBytes <= B` of `RelD0a B` at its boundary on real witnesses; B0 itself is far above
every generated case (see STATUS-V3-SPEC.md for the distribution).

usage: a7_boundary_v3.py --lean EXE --python FILE [--report OUT.json] CASE_DIR...
"""
import argparse, json, subprocess, sys


def run(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip().splitlines()
    return json.loads(out[-1])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", required=True)
    ap.add_argument("--python", required=True)
    ap.add_argument("--report")
    ap.add_argument("cases", nargs="+")
    a = ap.parse_args()
    stats = {"cases": 0, "skipped_not_in_d0a": 0, "ok": 0, "failures": []}
    for d in a.cases:
        base = run([a.lean, d])
        if base["verdict"] != "accept":
            stats["skipped_not_in_d0a"] += 1
            continue
        u = base["unfold"]
        stats["cases"] += 1
        res = {}
        for name, cmd in (("lean", [a.lean]), ("python", [sys.executable, a.python])):
            at = run(cmd + ["--bound", str(u), d])
            below = run(cmd + ["--bound", str(u - 1), d])
            res[name] = (at["verdict"], below["verdict"], below["reason"])
        good = all(v[0] == "accept" and v[1] == "out_of_domain" and "unfolded" in v[2] for v in res.values())
        if good:
            stats["ok"] += 1
        else:
            stats["failures"].append({"case": d, "unfold": u, "results": res})
    print(json.dumps({k: (v if k != "failures" else len(v)) for k, v in stats.items()}))
    if a.report:
        open(a.report, "w").write(json.dumps(stats, indent=1) + "\n")
    return 0 if not stats["failures"] else 1


if __name__ == "__main__":
    sys.exit(main())
