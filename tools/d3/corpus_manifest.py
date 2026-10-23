#!/usr/bin/env python3
"""Content manifest of the recorded regression corpora (plan §5 item 5: record hashes, not counts).

The plan requires the D1/D2/D3 regression corpora to be reproduced *and identified by content
hash*, so that a later run can prove it replayed the same bytes. This tool walks each corpus
family and hashes, in a fixed order, every case's `claim.bin`, `witness.bin` and `meta.json`.

  corpus_manifest.py [--corpora DIR] [--out FILE] [--verify FILE]

`--verify` re-walks the corpora and fails (exit 1) if any family's case count, byte total or digest
differs from the manifest — the drift gate. A missing family is reported, never silently dropped.

Digest definition (stable across hosts, order-dependent only through the sorted case names):

    for each case dir, sorted:  for f in (claim.bin, witness.bin, meta.json):
        sha256.update(f.encode()); sha256.update(len(data).to_bytes(8, "little")); sha256.update(data)

Note this binds the *input* bytes only. It does not bind a verdict; the verdict is the difftest's
output and is recorded separately by the lane log.
"""
import argparse
import hashlib
import json
import os
import sys

DEFAULT_CORPORA = "/data/illia/nearproof-deps/corpora"
FAMILIES = {
    "d1run": ("d1", "mutants", "ood"),
    "d2corpus.v2": ("d2", "mutants", "ood"),
    "d3c7": ("d3", "mutants", "ood"),
    "d3c8": ("d3", "mutants", "ood"),
    "d3c9": ("d3", "mutants", "ood"),
    "d3c10": ("d3", "mutants", "ood"),
}
EXPECTED = {"d1run": 53048, "d2corpus.v2": 67384, "d3c7": 33248, "d3c8": 49490,
            "d3c9": 15995, "d3c10": 16551}
FILES = ("claim.bin", "witness.bin", "meta.json")


def family_digest(path):
    h = hashlib.sha256()
    n = 0
    total = 0
    missing = []
    for name in sorted(os.listdir(path)):
        d = os.path.join(path, name)
        if not os.path.isdir(d):
            continue
        n += 1
        for f in FILES:
            fp = os.path.join(d, f)
            if not os.path.exists(fp):
                missing.append(f"{name}/{f}")
                continue
            data = open(fp, "rb").read()
            total += len(data)
            h.update(f.encode())
            h.update(len(data).to_bytes(8, "little"))
            h.update(data)
    return {"cases": n, "bytes": total, "sha256": h.hexdigest(), "missing_files": missing[:20],
            "missing_count": len(missing)}


def walk(corpora):
    out = {}
    for corpus, fams in FAMILIES.items():
        for fam in fams:
            p = os.path.join(corpora, corpus, fam)
            if not os.path.isdir(p):
                out[f"{corpus}/{fam}"] = {"absent": True}
                continue
            out[f"{corpus}/{fam}"] = family_digest(p)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpora", default=DEFAULT_CORPORA)
    ap.add_argument("--out", default=None)
    ap.add_argument("--verify", default=None)
    a = ap.parse_args()

    if not os.path.isdir(a.corpora):
        sys.exit(f"corpora directory not found: {a.corpora}")

    m = walk(a.corpora)
    totals = {}
    for corpus in FAMILIES:
        n = sum(v.get("cases", 0) for k, v in m.items() if k.startswith(corpus + "/"))
        totals[corpus] = n
    doc = {
        "schema": "near-l7-corpus-manifest-v1",
        "corpora_root": os.path.abspath(a.corpora),
        "digest_definition": ("per case dir (sorted): for f in claim.bin,witness.bin,meta.json: "
                              "sha256(f || u64le(len) || bytes)"),
        "expected_counts": EXPECTED,
        "measured_counts": totals,
        "families": m,
    }

    bad = []
    for corpus, want in EXPECTED.items():
        got = totals.get(corpus)
        if got != want:
            bad.append(f"{corpus}: {got} cases, the plan records {want}")

    if a.verify:
        ref = json.load(open(a.verify))
        for k, v in ref.get("families", {}).items():
            if m.get(k) != v:
                bad.append(f"{k}: digest/count drift vs {a.verify}")
        print(f"verify: compared {len(ref.get('families', {}))} families against {a.verify}")

    if a.out:
        with open(a.out, "w") as f:
            json.dump(doc, f, indent=1, sort_keys=True)
            f.write("\n")
        print(f"wrote {a.out}")

    for corpus in FAMILIES:
        fams = {k.split("/")[1]: m[k].get("cases") for k in m if k.startswith(corpus + "/")}
        print(f"{corpus:14s} total={totals[corpus]:6d}  {fams}")
        if totals[corpus] != EXPECTED[corpus]:
            print(f"  !! plan records {EXPECTED[corpus]}")

    if bad:
        print("\nMANIFEST MISMATCH:", file=sys.stderr)
        for b in bad:
            print(f"  - {b}", file=sys.stderr)
        return 1
    print("\nall corpora match the counts the plan records")
    return 0


if __name__ == "__main__":
    sys.exit(main())
