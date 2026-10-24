#!/usr/bin/env python3
"""Verify that Lean's emitted chunk outputs match an independent decode of the claim, per case.

`nearspec-v3-check-d3-out` prints, per case, the verdict and the consensus outputs it produced. Those
outputs are the endorsed header's fields, which the signed checker proved equal to the values it computed
(`NearSpecV3.accepted_observable_agrees`). This script checks the *emission* side independently: it
decodes each case's `claim.bin` in Python (`tools/d3/claim_outputs.py`) and compares field by field.

## What this establishes, and what it does not

**Establishes.** For every accepted case, the outputs Lean prints are byte-equal to the claim's endorsed
header fields. Because the signed checker compares its computed transition outputs against exactly those
fields and only accepts when they agree, an accepted case's printed outputs *are* the computed outputs —
so this verifies the emission path end to end without trusting Lean's decoder.

**Does not establish.** That the computed values equal what a *nearcore validator would recompute*. That
is the signed checker's job and is measured by the difftest verdicts (115,284/115,284 on D3). Nor does it
cover rejected cases: their printed `outputs` is null by design, because the signed checker does not expose
its computed values on a failing path. A rejected case is checked by its verdict and reason string only.

## Failure accounting

A field mismatch, a missing line, a non-JSON line, a crashed shard or an accepted case with null outputs is
a failure. An `out_of_domain` or `reject` case is *not* a failure here — its verdict is the difftest's
concern — but it is counted so the denominator is complete. Exit 0 only when no accepted case mismatches
and every case produced a line.
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../.."))
DRIVER = os.path.join(ROOT, "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out")

# Fields compared. `proposals` is a list of hex strings; everything else is scalar or hex.
SCALAR_FIELDS = [
    "stateRoot", "outcomeRoot", "gasBurnt", "balanceBurnt", "outgoingReceiptsRoot", "txRoot",
    "encodedMerkleRoot", "encodedLength",
]


def independent_outputs(claim_path):
    """Decode the claim in Python and return its output fields."""
    import importlib.util
    spec = importlib.util.spec_from_file_location("claim_outputs", os.path.join(HERE, "claim_outputs.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    claim = open(claim_path, "rb").read()
    c = mod.decode_claim(claim)
    ci = mod.decode_chunk_inner(c["chunk_inner"])
    return {
        "stateRoot": ci["prev_state_root"].hex(),
        "outcomeRoot": ci["prev_outcome_root"].hex(),
        "gasBurnt": ci["prev_gas_used"],
        "balanceBurnt": ci["prev_balance_burnt"],
        "outgoingReceiptsRoot": ci["prev_outgoing_receipts_root"].hex(),
        "proposals": [p.hex() for p in ci["proposals"]],
        "txRoot": ci["tx_root"].hex(),
        "encodedMerkleRoot": ci["encoded_merkle_root"].hex(),
        "encodedLength": ci["encoded_length"],
    }


def run_driver(cases, shards, timeout):
    """Run the Lean driver over all cases in `shards` parallel processes. Returns case -> line."""
    import tempfile
    got = {}
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for s in range(shards):
            part = cases[s::shards]
            if not part:
                continue
            out = open(os.path.join(td, f"out{s}"), "w")
            err = open(os.path.join(td, f"err{s}"), "w")
            procs.append((s, subprocess.Popen([DRIVER] + part, stdout=out, stderr=err,
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
    ap.add_argument("--families", default="d3", help="comma list of subdirectories to include")
    ap.add_argument("--shards", type=int, default=16)
    ap.add_argument("--timeout", type=float, default=0.0)
    ap.add_argument("--sample", type=int, default=0, help="randomly sample this many cases (0 = all)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--report", default=None, help="write a machine-readable JSON report here")
    args = ap.parse_args()

    fams = [f.strip() for f in args.families.split(",") if f.strip()]
    cases = []
    for fam in fams:
        d = os.path.join(args.corpus, fam)
        if not os.path.isdir(d):
            print(f"missing family dir {d}", file=sys.stderr)
            return 2
        for c in sorted(os.listdir(d)):
            p = os.path.join(d, c)
            if os.path.isfile(os.path.join(p, "claim.bin")):
                cases.append(p)
    if args.sample and args.sample < len(cases):
        import random
        rng = random.Random(args.seed)
        cases = rng.sample(cases, args.sample)
    print(f"cases read: {len(cases)} ({','.join(fams)})", file=sys.stderr)
    if not cases:
        return 2

    got = run_driver(cases, args.shards, args.timeout)

    counts = {"accept": 0, "reject": 0, "out_of_domain": 0}
    mismatches = []
    accept_no_outputs = []
    missing = []
    per_field = {}

    for p in cases:
        j = got.get(p)
        if j is None:
            missing.append(p)
            continue
        v = j.get("verdict", "?")
        counts[v] = counts.get(v, 0) + 1
        if v != "accept":
            continue
        outs = j.get("outputs")
        if outs is None:
            accept_no_outputs.append(p)
            continue
        try:
            ind = independent_outputs(os.path.join(p, "claim.bin"))
        except Exception as e:  # noqa: BLE001
            mismatches.append({"case": p, "field": "<decode>", "lean": None, "claim": str(e)})
            continue
        for f in SCALAR_FIELDS:
            if outs.get(f) != ind.get(f):
                per_field[f] = per_field.get(f, 0) + 1
                mismatches.append({"case": p, "field": f, "lean": outs.get(f), "claim": ind.get(f)})
        if outs.get("proposals") != ind.get("proposals"):
            per_field["proposals"] = per_field.get("proposals", 0) + 1
            mismatches.append({"case": p, "field": "proposals",
                               "lean": len(outs.get("proposals") or []),
                               "claim": len(ind.get("proposals") or [])})

    total_bad = len(mismatches) + len(accept_no_outputs) + len(missing)
    print()
    print(f"verdicts: {counts}")
    print(f"accepted with outputs: {counts.get('accept', 0) - len(accept_no_outputs)}")
    print(f"field mismatches: {len(mismatches)}" + (f" {per_field}" if per_field else ""))
    print(f"accepted but null outputs: {len(accept_no_outputs)}")
    print(f"missing lines: {len(missing)}")
    print(f"TOTAL FAILURES: {total_bad}")
    for m in mismatches[:15]:
        print(f"  MISMATCH {os.path.basename(m['case'])} {m['field']}: lean={m['lean']} claim={m['claim']}")
    for p in accept_no_outputs[:5]:
        print(f"  NO OUTPUTS {os.path.basename(p)}")
    for p in missing[:5]:
        print(f"  MISSING {os.path.basename(p)}")

    if args.report:
        doc = {
            "schema": "near-d3-output-agreement-v1",
            "corpus": os.path.abspath(args.corpus),
            "families": fams,
            "cases_read": len(cases),
            "driver": DRIVER,
            "verdicts": counts,
            "accepted_with_outputs": counts.get("accept", 0) - len(accept_no_outputs),
            "field_mismatches": len(mismatches),
            "mismatches_by_field": per_field,
            "mismatches": mismatches[:200],
            "accepted_null_outputs": accept_no_outputs[:200],
            "missing_lines": missing[:200],
            "total_failures": total_bad,
        }
        with open(args.report, "w") as f:
            json.dump(doc, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"wrote {args.report}")
    return 0 if total_bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
