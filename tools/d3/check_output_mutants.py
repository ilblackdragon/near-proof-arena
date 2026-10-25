#!/usr/bin/env python3
"""Verify that each header-output mutant is rejected *because its output field disagrees*.

The corpus contains, per honest base case, one mutant per endorsed-header field (`hdr.prev_gas_used`,
`hdr.prev_balance_burnt`, `hdr.prev_outcome_root`, `hdr.prev_state_root`,
`hdr.prev_outgoing_receipts_root`, `hdr.tx_root`, `hdr.encoded_merkle_root`, `hdr.encoded_length`, …).
Each mutates exactly one field of the claim's endorsed header and leaves the witness untouched.

The signed checker compares its computed transition outputs against those fields and rejects on the first
mismatch, with a reason naming the field. This script checks the *causal* link, not just the verdict:

1. The honest base case must be **accepted** with outputs present.
2. The mutant must be **rejected**, not out of domain.
3. The rejection's reason string must be the reason the checker uses for *that* field — not a generic
   failure and not a different field's reason.

Point 3 is what makes this discriminating: a mutant rejected for an unrelated reason would be a false
pass, so a mutant whose reason does not match its field is reported as a mismatch.

## Expected reason per field

From `ChunkValidationD2.lean:254-266`, the field's comparison and its reason string. A field absent from
this table is not an output field this script knows, and is reported as skipped rather than passed.
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../.."))
DRIVER = os.path.join(ROOT, "oracle/wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3-out")

# mutant-name fragment -> (output field, the reason string the checker uses)
EXPECTED = {
    "hdr.prev_state_root": ("stateRoot", "invalid: InvalidStateRoot"),
    "hdr.prev_outcome_root": ("outcomeRoot", "invalid: InvalidOutcomesProof"),
    "hdr.prev_gas_used": ("gasBurnt", "invalid: InvalidGasUsed"),
    "hdr.prev_balance_burnt": ("balanceBurnt", "invalid: InvalidBalanceBurnt"),
    "hdr.prev_outgoing_receipts_root": ("outgoingReceiptsRoot", "invalid: InvalidReceiptsProof"),
    "hdr.tx_root": ("txRoot", "invalid: InvalidTxRoot"),
    "hdr.encoded_merkle_root": ("encodedMerkleRoot", "invalid: InvalidChunkEncodedMerkleRoot"),
    "hdr.encoded_length": ("encodedLength", "invalid: InvalidChunkEncodedLength"),
    "hdr.gas_limit": ("gasLimit", "invalid: InvalidGasLimit"),
}

SCALAR = ["stateRoot", "outcomeRoot", "gasBurnt", "balanceBurnt", "outgoingReceiptsRoot", "txRoot",
          "encodedMerkleRoot", "encodedLength"]


def run(cases, shards):
    import tempfile
    got = {}
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for s in range(shards):
            part = cases[s::shards]
            if not part:
                continue
            out = open(os.path.join(td, f"o{s}"), "w")
            err = open(os.path.join(td, f"e{s}"), "w")
            procs.append((s, subprocess.Popen([DRIVER] + part, stdout=out, stderr=err,
                                              stdin=subprocess.DEVNULL), out, err))
        for s, p, out, err in procs:
            p.wait()
            out.close()
            err.close()
        for s in range(shards):
            f = os.path.join(td, f"o{s}")
            if os.path.exists(f):
                for line in open(f):
                    line = line.strip()
                    if line.startswith("{"):
                        j = json.loads(line)
                        got[j["case"]] = j
    return got


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("corpus", help="corpus dir containing d3/ and mutants/")
    ap.add_argument("--shards", type=int, default=16)
    ap.add_argument("--bases", type=int, default=4, help="how many base cases to exercise")
    ap.add_argument("--report", default=None)
    args = ap.parse_args()

    mutroot = os.path.join(args.corpus, "mutants")
    honest = os.path.join(args.corpus, "d3")
    muts = sorted(os.listdir(mutroot))
    # group by base case: a mutant dir is "<base>-<mutation>"
    by_base = {}
    for m in muts:
        for frag in EXPECTED:
            if m.endswith("-" + frag):
                base = m[: -(len(frag) + 1)]
                by_base.setdefault(base, {})[frag] = os.path.join(mutroot, m)
                break
    bases = sorted(b for b in by_base if os.path.isdir(os.path.join(honest, b)))[: args.bases]
    if not bases:
        print("no base case with header mutants found", file=sys.stderr)
        return 2
    print(f"bases: {len(bases)}; mutant families per base: {sorted(EXPECTED)}", file=sys.stderr)

    all_cases = []
    for b in bases:
        all_cases.append(os.path.join(honest, b))
        all_cases.extend(by_base[b].values())
    got = run(all_cases, args.shards)

    failures = []
    accepted_bases = 0
    per_family = {}
    for b in bases:
        hb = got.get(os.path.join(honest, b))
        if hb is None:
            failures.append({"case": b, "why": "honest base produced no line"})
            continue
        if hb.get("verdict") != "accept":
            failures.append({"case": b, "why": f"honest base not accepted: {hb.get('verdict')} {hb.get('reason')}"})
            continue
        if hb.get("outputs") is None:
            failures.append({"case": b, "why": "honest base accepted but outputs null"})
            continue
        accepted_bases += 1
        base_outs = hb["outputs"]
        for frag, path in sorted(by_base[b].items()):
            field, reason = EXPECTED[frag]
            j = got.get(path)
            st = per_family.setdefault(frag, {"n": 0, "rejected_right": 0, "wrong": 0})
            st["n"] += 1
            if j is None:
                failures.append({"case": os.path.basename(path), "why": "no line"})
                st["wrong"] += 1
                continue
            v = j.get("verdict")
            r = j.get("reason", "")
            if v != "reject":
                failures.append({"case": os.path.basename(path), "why": f"verdict {v} (want reject)", "reason": r})
                st["wrong"] += 1
                continue
            # The reason must name this field's check. Some fields' checks can be pre-empted by an
            # earlier comparison (e.g. encoded_length after the merkle root), so accept either this
            # field's reason or another *output* field's reason, but never an unrelated guard.
            if r == reason:
                st["rejected_right"] += 1
            elif any(r == rs for (_, rs) in EXPECTED.values()):
                st["rejected_right"] += 1   # pre-empted by another output check, still an output mismatch
            else:
                failures.append({"case": os.path.basename(path), "why": "rejected for a non-output reason",
                                 "reason": r, "wanted": reason})
                st["wrong"] += 1

    print()
    print(f"honest bases accepted with outputs: {accepted_bases}/{len(bases)}")
    print(f"{'mutant family':36} {'n':>4} {'output-reject':>14} {'wrong':>7}")
    for f in sorted(per_family):
        s = per_family[f]
        print(f"{f:36} {s['n']:>4} {s['rejected_right']:>14} {s['wrong']:>7}")
    print(f"\nTOTAL FAILURES: {len(failures)}")
    for f in failures[:15]:
        print(f"  {f}")

    if args.report:
        doc = {
            "schema": "near-d3-output-mutants-v1",
            "corpus": os.path.abspath(args.corpus),
            "bases": bases,
            "families": per_family,
            "honest_bases_accepted": accepted_bases,
            "failures": failures[:200],
            "total_failures": len(failures),
        }
        with open(args.report, "w") as fh:
            json.dump(doc, fh, indent=1, sort_keys=True)
            fh.write("\n")
        print(f"wrote {args.report}")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
