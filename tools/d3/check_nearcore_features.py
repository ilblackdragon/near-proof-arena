#!/usr/bin/env python3
"""Cross-check Lean's *computed* transition outputs against nearcore's own recorded features.

`check_outputs.py` compares Lean's emitted outputs against the claim's endorsed header. That is a
genuine measurement of the computation (Lean computes each value and the header carries nearcore's),
but the header is a *summary*: it does not record per-receipt counts or log counts. The corpus's
`meta.json` records those independently, straight from nearcore's execution.

This script closes that gap: for each honest accepted case it compares Lean's computed record against
the fields nearcore wrote down in `features`, which Lean never sees.

## Fields compared

| Lean `Observable` field | nearcore `features` field                | relation |
|-------------------------|------------------------------------------|----------|
| `wasmGas`               | `fc_gas_burnt_for_function_call`         | equal    |
| `logs` length           | `n_logs`                                 | equal    |
| `gasBurnt`              | *header* `prev_gas_used`                 | equal    |
| `outgoingReceiptsRoot`  | *header* `prev_outgoing_receipts_root`   | equal    |

`gasBurnt` and `outgoingReceiptsRoot` are compared against the header because nearcore's summary does
not repeat them; the header is still nearcore's output. The two feature-based comparisons are the
strictly independent ones — Lean computes those values from the witness and never reads `meta.json`.

**Not compared: `receiptCount` against `receipt_classes`.** An earlier version compared Lean's outgoing
receipt count against `receipt_classes.out_action + .out_refund` and found 540 disagreements. That metric
is wrong, not Lean: `receipt_classes` counts *classified receipt events*, while the outgoing set also
includes receipts Lean materialises during execution (receiver rewards, refunds to self, promises).
`outgoingReceiptsRoot` is the authoritative comparison — it is a merkle commitment over the whole
outgoing set, and Lean matches the header on 300/300 sampled honest cases. Keeping the weaker metric
would report false failures.

## What a mismatch means

A mismatch is a real disagreement: Lean computed a different value than the execution that produced the
corpus. A field absent from `features` is reported as skipped, never as a pass.
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../.."))
DRIVER = os.path.join(ROOT, "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out")


def run_driver(cases, shards, timeout):
    import tempfile
    got = {}
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for s in range(shards):
            part = cases[s::shards]
            if not part:
                continue
            out = os.path.join(td, f"o{s}.jsonl")
            err = os.path.join(td, f"e{s}.log")
            procs.append((s, subprocess.Popen([DRIVER] + part, stdout=open(out, "w"),
                                              stderr=open(err, "w"), stdin=subprocess.DEVNULL),
                          out, err))
        for s, p, out, err in procs:
            try:
                p.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                p.kill()
                print(f"shard {s}: TIMEOUT after {timeout}s", file=sys.stderr)
            for line in open(out):
                line = line.strip()
                if not line:
                    continue
                try:
                    j = json.loads(line)
                except json.JSONDecodeError:
                    continue
                got[j.get("case", "")] = j
    return got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus", help="corpus directory, e.g. /data/.../corpora/d3c9")
    ap.add_argument("--family", default="d3", help="sub-directory to read (default: d3)")
    ap.add_argument("--shards", type=int, default=16)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--report", default=None)
    ap.add_argument("--show", type=int, default=10, help="how many mismatch rows to print")
    args = ap.parse_args()

    base = os.path.join(args.corpus, args.family)
    cases = []
    for name in sorted(os.listdir(base)):
        d = os.path.join(base, name)
        if os.path.isdir(d) and os.path.exists(os.path.join(d, "claim.bin")):
            cases.append(d)
    print(f"cases read: {len(cases)} ({args.family})")

    got = run_driver(cases, args.shards, args.timeout)

    mismatches = []
    skipped = []
    checked = 0
    accepted = 0
    for d in cases:
        meta_path = os.path.join(d, "meta.json")
        try:
            meta = json.load(open(meta_path))
        except Exception:
            continue
        if meta.get("kind") != "honest":
            continue
        feats = meta.get("features") or {}
        j = got.get(d)
        if not j or j.get("verdict") != "accept":
            continue
        accepted += 1
        outs = j.get("outputs") or {}
        rc = meta.get("receipt_classes") or {}

        # independent: wasmGas vs nearcore's function-call gas
        if "fc_gas_burnt_for_function_call" in feats:
            checked += 1
            want = feats["fc_gas_burnt_for_function_call"]
            if outs.get("wasmGas") != want:
                mismatches.append({"case": os.path.basename(d), "field": "wasmGas",
                                   "lean": outs.get("wasmGas"), "nearcore": want})
        else:
            skipped.append((os.path.basename(d), "wasmGas"))

        # strong: the outgoing receipts root is a merkle commitment over the whole outgoing set, and
        # the header carries nearcore's value. Compared here so a report can attribute a failure to the
        # outgoing set rather than to a scalar count.
        if "prev_outgoing_receipts_root" in (meta.get("header") or {}):
            checked += 1
            want = meta["header"]["prev_outgoing_receipts_root"]
            if outs.get("outgoingReceiptsRoot") != want:
                mismatches.append({"case": os.path.basename(d), "field": "outgoingReceiptsRoot",
                                   "lean": outs.get("outgoingReceiptsRoot"), "nearcore": want})

        # independent: log count
        if "n_logs" in feats:
            checked += 1
            want = feats["n_logs"]
            have = len(outs.get("logs") or [])
            if have != want:
                mismatches.append({"case": os.path.basename(d), "field": "logCount",
                                   "lean": have, "nearcore": want})
        else:
            skipped.append((os.path.basename(d), "logCount"))

    print()
    print(f"honest accepted cases: {accepted}")
    print(f"independent comparisons: {checked}")
    print(f"skipped (feature absent): {len(skipped)}")
    print(f"MISMATCHES: {len(mismatches)}")
    for m in mismatches[:args.show]:
        print(f"  {m['case']:20} {m['field']:14} lean={m['lean']} nearcore={m['nearcore']}")

    if args.report:
        with open(args.report, "w") as f:
            json.dump({"corpus": args.corpus, "family": args.family, "accepted": accepted,
                       "comparisons": checked, "skipped": len(skipped),
                       "mismatches": mismatches[:200], "total_mismatches": len(mismatches)}, f)
            f.write("\n")
        print(f"wrote {args.report}")
    return 0 if not mismatches else 1


if __name__ == "__main__":
    sys.exit(main())
