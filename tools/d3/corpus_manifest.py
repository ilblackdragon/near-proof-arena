#!/usr/bin/env python3
"""Content manifest of the recorded regression corpora (plan §5 item 5: record hashes, not counts).

The plan requires the D1/D2/D3 regression corpora to be reproduced *and identified by content
hash*, so that a later run can prove it replayed the same bytes. This tool walks each corpus
family and hashes, in a fixed order, every case's `claim.bin`, `witness.bin` and `meta.json`.

  corpus_manifest.py [--corpora DIR] [--out FILE] [--verify FILE] [--verify-schema FILE]

Modes, deliberately kept distinct (workplan W01: "a schema-only manifest test may run without
corpora but must not be called a corpus-content drift check"):

  --verify-schema FILE   Validate the *shape* of a committed manifest document. Reads no corpus
                         bytes. Always runnable, including on a hosted runner with no corpora.
  --verify FILE          Re-walk the corpora and fail (exit 1) if any family's case count, byte
                         total or digest differs from the manifest — the content drift gate.
                         Requires --corpora (or NEAR_CORPORA_DIR) and an existing directory.
  --out FILE             Write a freshly generated manifest.

The corpora root is never taken from a hardcoded developer path: pass `--corpora DIR` or set
`NEAR_CORPORA_DIR`. A content check with no configured root is a usage error (exit 2), which is a
different failure from a configured-but-absent root (exit 1). The manifest's recorded
`corpora_root` is provenance only and is not compared against the current host path.

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

SCHEMA = "near-l7-corpus-manifest-v1"
DEFAULT_CORPORA = os.environ.get("NEAR_CORPORA_DIR")
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

REQUIRED_TOP = ("schema", "corpora_root", "digest_definition", "expected_counts",
                "measured_counts", "families")


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


def schema_errors(doc):
    """Shape errors in a manifest document. Reads no corpus bytes.

    Deliberately *not* a content check: it cannot tell whether a digest matches the bytes on this
    host, only whether the document is a well-formed manifest. The two checks are separate commands
    so neither is ever reported as the other."""
    errs = []
    if not isinstance(doc, dict):
        return ["manifest is not a JSON object"]
    for k in REQUIRED_TOP:
        if k not in doc:
            errs.append(f"missing top-level key: {k}")
    if doc.get("schema") != SCHEMA:
        errs.append(f"schema is {doc.get('schema')!r}, expected {SCHEMA!r}")
    if not isinstance(doc.get("corpora_root"), str) or not doc.get("corpora_root"):
        errs.append("corpora_root must be a non-empty string (provenance only)")
    if not isinstance(doc.get("digest_definition"), str) or not doc.get("digest_definition"):
        errs.append("digest_definition must be a non-empty string")
    for key in ("expected_counts", "measured_counts"):
        d = doc.get(key)
        if not isinstance(d, dict) or not d:
            errs.append(f"{key} must be a non-empty object")
            continue
        for k, v in d.items():
            if not isinstance(k, str) or not isinstance(v, int) or isinstance(v, bool) or v < 0:
                errs.append(f"{key}[{k!r}] must be a non-negative integer")
    fams = doc.get("families")
    if not isinstance(fams, dict) or not fams:
        errs.append("families must be a non-empty object")
    else:
        for name, fam in fams.items():
            if not isinstance(fam, dict):
                errs.append(f"families[{name!r}] must be an object")
                continue
            if fam.get("absent") is True:
                continue
            for k in ("cases", "bytes", "missing_count"):
                if not isinstance(fam.get(k), int) or isinstance(fam.get(k), bool) or fam.get(k) < 0:
                    errs.append(f"families[{name!r}].{k} must be a non-negative integer")
            sha = fam.get("sha256")
            if not isinstance(sha, str) or len(sha) != 64 or any(c not in "0123456789abcdef" for c in sha):
                errs.append(f"families[{name!r}].sha256 must be 64 lowercase hex characters")
            mf = fam.get("missing_files")
            if not isinstance(mf, list) or not all(isinstance(x, str) for x in mf):
                errs.append(f"families[{name!r}].missing_files must be a list of strings")
    # expected_counts and measured_counts must name the same corpora as the families map.
    fam_corpora = {k.split("/", 1)[0] for k in fams} if isinstance(fams, dict) else set()
    for key in ("expected_counts", "measured_counts"):
        d = doc.get(key)
        if isinstance(d, dict):
            for k in d:
                if k not in fam_corpora:
                    errs.append(f"{key}[{k!r}] names a corpus with no families")
    return errs


def verify_content(doc, corpora):
    """Content drift errors: re-walk the corpora and compare every family field."""
    errs = []
    ref_fams = doc.get("families") or {}
    measured = walk(corpora)
    totals = {}
    for corpus in FAMILIES:
        totals[corpus] = sum(v.get("cases", 0) for k, v in measured.items() if k.startswith(corpus + "/"))
    for k, ref in ref_fams.items():
        got = measured.get(k)
        if got is None:
            errs.append(f"{k}: family is in the manifest but not a configured family")
            continue
        if got.get("absent"):
            errs.append(f"{k}: corpus directory absent")
            continue
        if ref.get("absent"):
            errs.append(f"{k}: manifest says absent but the corpus directory exists")
            continue
        for field in ("cases", "bytes", "sha256", "missing_count"):
            if ref.get(field) != got.get(field):
                errs.append(f"{k}.{field}: manifest {ref.get(field)!r} != measured {got.get(field)!r}")
    for k in measured:
        if k not in ref_fams:
            errs.append(f"{k}: measured family is absent from the manifest")
    for corpus, want in (doc.get("expected_counts") or {}).items():
        if totals.get(corpus) != want:
            errs.append(f"{corpus}: measured {totals.get(corpus)} cases, manifest records {want}")
    return errs, measured, totals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpora", default=DEFAULT_CORPORA,
                    help="corpora root (or set NEAR_CORPORA_DIR); required for content operations")
    ap.add_argument("--out", default=None, help="write a freshly generated manifest")
    ap.add_argument("--verify", default=None, help="content drift gate against this manifest")
    ap.add_argument("--verify-schema", default=None,
                    help="corpus-free manifest shape check against this manifest")
    a = ap.parse_args()

    if a.verify_schema:
        try:
            doc = json.load(open(a.verify_schema))
        except (OSError, json.JSONDecodeError) as e:
            print(f"SCHEMA MISMATCH: cannot read {a.verify_schema}: {e}", file=sys.stderr)
            return 1
        errs = schema_errors(doc)
        if errs:
            print("SCHEMA MISMATCH:", file=sys.stderr)
            for e in errs:
                print(f"  - {e}", file=sys.stderr)
            return 1
        print(f"schema ok: {a.verify_schema} "
              f"({len(doc.get('families', {}))} families, {len(doc.get('expected_counts', {}))} corpora)")
        return 0

    needs_corpora = a.out or a.verify or not a.verify_schema
    if needs_corpora and not a.corpora:
        print("corpora root not configured: pass --corpora DIR or set NEAR_CORPORA_DIR "
              "(a manifest schema check needs neither: --verify-schema FILE)", file=sys.stderr)
        return 2
    if needs_corpora and not os.path.isdir(a.corpora):
        print(f"corpora directory not found: {a.corpora}", file=sys.stderr)
        return 1

    m = walk(a.corpora)
    totals = {}
    for corpus in FAMILIES:
        n = sum(v.get("cases", 0) for k, v in m.items() if k.startswith(corpus + "/"))
        totals[corpus] = n
    doc = {
        "schema": SCHEMA,
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
        serrs = schema_errors(ref)
        if serrs:
            bad.append(f"manifest {a.verify} is malformed: {serrs[0]}")
        cerrs, _, _ = verify_content(ref, a.corpora)
        bad.extend(cerrs)
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
