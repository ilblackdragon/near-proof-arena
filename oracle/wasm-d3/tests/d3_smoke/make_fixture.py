#!/usr/bin/env python3
"""Build the committed D3 smoke fixture from a pinned corpora copy.

The committed fixture is a tiny, self-contained set of case directories (claim.bin, witness.bin,
meta.json) copied verbatim from the L7 regression corpora. It exists so CI can *run* the D3 drivers
(checkD3, checkD3F, checkD3G, checkD3Proto) and the difftest's comparison contract without the
8.5 GiB corpora. It is NOT a substitute for the full sweep: seven cases, covering every verdict/domain
class and each widening family a driver lifts.

  python3 oracle/wasm-d3/tests/d3_smoke/make_fixture.py --corpora /data/illia/nearproof-deps/corpora \
      --out oracle/wasm-d3/tests/d3_smoke/cases

The expected verdicts are recomputed from the oracle's meta.json, not copied from a checker run, so a
checker regression shows up as a mismatch instead of being baked into the fixture.
"""
import argparse
import json
import os
import shutil

# (corpus, family, case, why) — chosen by scanning the corpora for one case per class.
SELECTION = [
    ("d3c7", "d3", "00-h10004-s1", "in-domain accept"),
    ("d3c7", "mutants", "00-h10004-s2-code.drop.0", "in-domain reject"),
    ("d3c7", "mutants", "00-h10153-s0-code.drop.1", "code-cache exclusion"),
    ("d3c7", "ood", "00-h10002-s0", "c.not_genesis exclusion (successor d3g accepts)"),
    ("d3c7", "ood", "00-h10006-s2", "e.ood_host exclusion"),
    ("d3c9", "ood", "00-h10072-s3",
     "e.float exclusion: baseline/float-absent drivers exclude, d3f accepts"),
    ("d3c7", "ood", "00-h10007-s1",
     "e.g_alpha band exclusion: d3/d3f/d3g exclude, d3proto accepts"),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpora", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    index = []
    for corpus, fam, case, why in SELECTION:
        src = os.path.join(a.corpora, corpus, fam, case)
        if not os.path.isdir(src):
            raise SystemExit(f"missing source case: {src}")
        dst = os.path.join(a.out, f"{corpus}-{fam}-{case}")
        if os.path.isdir(dst):
            shutil.rmtree(dst)
        os.makedirs(dst)
        for f in ("claim.bin", "witness.bin", "meta.json"):
            shutil.copyfile(os.path.join(src, f), os.path.join(dst, f))
        meta = json.load(open(os.path.join(dst, "meta.json")))
        index.append({
            "case_dir": os.path.basename(dst),
            "source": f"{corpus}/{fam}/{case}",
            "why": why,
            "expected_rel": bool(meta.get("expected_rel")),
            "in_d3": bool(meta.get("in_d3")),
            "d3_violations": list(meta.get("d3_violations") or []),
        })
    with open(os.path.join(a.out, "index.json"), "w") as f:
        json.dump({
            "schema": "near-d3-smoke-fixture-v2",
            "note": ("Seven real D3 cases copied from the L7 corpora. Expected verdicts come from the "
                     "oracle's meta.json; each driver is compared against its own declared "
                     "expectation domain, so a driver that stops widening (or widens wrongly) fails. "
                     "Run by CI to exercise the drivers and the comparison contract; not a "
                     "substitute for the full 115,284-case sweep."),
            "cases": index,
        }, f, indent=1, sort_keys=True)
        f.write("\n")
    print(f"wrote {len(index)} cases and index.json under {a.out}")


if __name__ == "__main__":
    main()
