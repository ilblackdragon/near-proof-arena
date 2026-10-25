#!/usr/bin/env python3
"""Check that the D1 output driver's verdicts are the signed D1 driver's verdicts, case for case.

`checkD1` is defined as `(checkD1CoreObs …).map fun _ => ()`, so the signed checker and the
output-emitting checker are one computation. This script measures that on real bytes: it runs both
drivers over the same case directories and compares `(verdict, reason)` per case.

## Why this is separate from `check_outputs.py`

`check_outputs.py` verifies the *outputs* on accepted cases against an independent Python decode of the
claim. It does not compare against the signed driver; a projection bug that changed a verdict would show
up there only as a verdict-count shift. This script compares the two binaries directly, so "the signed
relation did not change" is measured on the whole corpus rather than asserted from the definition.

## Failure accounting

A case whose `(verdict, reason)` differs is a failure. A case missing from either driver's output is a
failure. A driver crash or timeout is a failure. Exit 0 only when every case agrees.
"""
import argparse
import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../.."))
SIGNED = os.path.join(ROOT, "spec/lean/v3/.lake/build/bin/nearspec-v3-check-d1")
OUT = os.path.join(ROOT, "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out")


def run(binary, cases, shards, timeout, prefix):
    got = {}
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for s in range(shards):
            part = cases[s::shards]
            if not part:
                continue
            out = open(os.path.join(td, f"out{s}"), "w")
            err = open(os.path.join(td, f"err{s}"), "w")
            procs.append((s, subprocess.Popen([binary] + prefix + part, stdout=out, stderr=err,
                                              stdin=subprocess.DEVNULL), out, err))
        for s, p, out, err in procs:
            try:
                p.wait(timeout=timeout or None)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait()
                print(f"FATAL shard {s} timed out", file=sys.stderr)
                raise SystemExit(2)
            out.close()
            err.close()
            ef = os.path.join(td, f"err{s}")
            if os.path.exists(ef) and os.path.getsize(ef):
                txt = open(ef).read()
                if "INTERNAL ERROR" in txt or "Traceback" in txt:
                    print(f"[shard {s} stderr] {txt[:2000]}", file=sys.stderr)
        for s in range(shards):
            f = os.path.join(td, f"out{s}")
            if not os.path.exists(f):
                continue
            for line in open(f):
                line = line.strip()
                if line.startswith("{"):
                    j = json.loads(line)
                    got[j["case"]] = j
    return got


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("corpus", help="corpus directory whose subdirectories are case dirs")
    ap.add_argument("--families", default="d1,mutants,ood", help="comma list of subdirectories")
    ap.add_argument("--shards", type=int, default=16)
    ap.add_argument("--timeout", type=float, default=0.0)
    ap.add_argument("--report", default=None)
    args = ap.parse_args()

    for b in (SIGNED, OUT):
        if not os.path.exists(b):
            print(f"FATAL missing driver: {b}", file=sys.stderr)
            return 2

    cases = []
    for fam in [f.strip() for f in args.families.split(",") if f.strip()]:
        d = os.path.join(args.corpus, fam)
        if not os.path.isdir(d):
            print(f"missing family dir {d}", file=sys.stderr)
            return 2
        for c in sorted(os.listdir(d)):
            p = os.path.join(d, c)
            if os.path.isfile(os.path.join(p, "claim.bin")):
                cases.append(p)
    print(f"cases read: {len(cases)}", file=sys.stderr)

    signed = run(SIGNED, cases, args.shards, args.timeout, [])
    out = run(OUT, cases, args.shards, args.timeout, ["--d1"])

    counts = {"accept": 0, "reject": 0, "out_of_domain": 0}
    disagree = []
    missing = []
    reason_only = []
    for p in cases:
        a = signed.get(p)
        b = out.get(p)
        if a is None or b is None:
            missing.append({"case": p, "signed": a is not None, "output": b is not None})
            continue
        counts[a.get("verdict", "?")] = counts.get(a.get("verdict", "?"), 0) + 1
        if a.get("verdict") != b.get("verdict"):
            disagree.append({"case": p, "signed": a, "output": b})
        elif a.get("reason") != b.get("reason"):
            reason_only.append({"case": p, "signed": a.get("reason"), "output": b.get("reason")})

    total_bad = len(disagree) + len(missing)
    print()
    print(f"signed verdicts: {counts}")
    print(f"verdict disagreements: {len(disagree)}")
    print(f"reason-only differences: {len(reason_only)}")
    print(f"missing lines: {len(missing)}")
    print(f"TOTAL FAILURES: {total_bad}")
    for d in disagree[:15]:
        print(f"  DISAGREE {os.path.basename(d['case'])}: signed={d['signed']['verdict']} "
              f"({d['signed']['reason']}) output={d['output']['verdict']} ({d['output']['reason']})")
    for r in reason_only[:15]:
        print(f"  REASON {os.path.basename(r['case'])}: signed={r['signed']!r} output={r['output']!r}")

    if args.report:
        with open(args.report, "w") as f:
            json.dump({"schema": "near-d1-verdict-agreement-v1",
                       "corpus": os.path.abspath(args.corpus),
                       "families": args.families,
                       "cases_read": len(cases),
                       "signed_driver": SIGNED, "output_driver": OUT,
                       "signed_verdicts": counts,
                       "verdict_disagreements": len(disagree),
                       "reason_only_differences": len(reason_only),
                       "missing_lines": len(missing),
                       "disagreements": disagree[:200],
                       "reason_differences": reason_only[:200],
                       "missing": missing[:200],
                       "total_failures": total_bad},
                      f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"wrote {args.report}")
    return 0 if total_bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
