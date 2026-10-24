#!/usr/bin/env python3
"""Replay the recorded D3 corpus through `checkD3` (D3α) and `checkD3F` (L2 floats).

    python3 tools/d3/replay_d3_float.py --corpora DIR [--out DIR] [--jobs N] [--limit N]

For every case directory under `DIR/{d3,mutants,ood}/*/` (the recorded 115,284-case corpus, or a
subsample with `--limit`), it runs

  * `nearspec-v3-check-d3`  — the signed D3α checker, and
  * `nearspec-v3-check-d3f` — the L2 extension,

and then reports, against each case's `meta.json`:

  * **D3α regression:** the same comparison `docs`/`var/d3-runs/make_report.py` makes (a Lean
    `out_of_domain` on an in-D3α case is a disagreement; accept/reject must match
    `meta.expected_rel`; the `e.g_alpha` and `e.code_cache` conditions must coincide with the
    oracle's violation marks). The L2 lane must not move any of these.
  * **Float-domain delta:** cases whose verdict changes between the two checkers. Every change must
    be `out_of_domain → accept|reject` on a case whose `d3_violations` contain `e.float`, and the
    new verdict must equal `meta.expected_rel` (nearcore's own verdict). Anything else is reported
    as a bug in the extension.

Exit 1 on any D3α regression, or any float-delta that is not the expected `e.float` acceptance.
"""
import argparse
import collections
import concurrent.futures
import json
import os
import subprocess
import sys

from replay_successor import run_batch, load_compare

BIN = os.environ.get(
    "D3_BIN",
    os.path.join(os.path.dirname(os.path.abspath(__file__)),
                 "../../oracle/wasm-d3/lean/.lake/build/bin"))
G_ALPHA = 2 ** 22 * 822756


def boundary(reason):
    r = reason or ""
    if "code_cache" in r or "compiled-contract cache" in r:
        return "code_cache"
    if "g_alpha" in r or "gAlpha" in r or "G_α" in r or "e_alpha" in r:
        return "g_alpha"
    return None


def d3_disagreement(fam, m, g):
    """The comparison of `var/d3-runs/make_report.py`, unchanged."""
    v = g.get("verdict", "missing")
    near = m.get("expected_rel")
    viol = m.get("d3_violations") or []
    ind3 = m.get("in_d3", m.get("expected_rel_d3") is not None and not viol)
    b = boundary(g.get("reason")) if v == "out_of_domain" else None
    o_ga, c_ga = "e.g_alpha" in viol, b == "g_alpha"
    if (c_ga and not o_ga) or (o_ga and v == "accept"):
        return f"G_alpha: oracle={o_ga} lean={v}"
    o_cc, c_cc = "e.code_cache" in viol, b == "code_cache"
    if o_cc != c_cc:
        return f"code_cache: oracle={o_cc} lean={v}"
    if v == "out_of_domain":
        if ind3 and fam != "ood":
            return f"lean out_of_domain on an in-D3a case: {g.get('reason')}"
        return None
    if v == "missing":
        return "lean produced no verdict"
    if (v == "accept") != bool(near):
        return f"lean {v} vs nearcore {near}"
    return None


def run(binary, dirs):
    return run_batch([binary], dirs, timeout=600)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpora", default="/data/illia/nearproof-deps/corpora")
    ap.add_argument("--out", default="/tmp/opencode/d3replay")
    ap.add_argument("--jobs", type=int, default=12)
    ap.add_argument("--limit", type=int, default=0, help="per corpus family (0 = all)")
    ap.add_argument("--chunk", type=int, default=100)
    ap.add_argument("--corpus-list", default="d3c7,d3c8,d3c9,d3c10")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    cases = []
    for c in a.corpus_list.split(","):
        for fam in ("d3", "mutants", "ood"):
            d = os.path.join(a.corpora, c, fam)
            if not os.path.isdir(d):
                continue
            names = sorted(n for n in os.listdir(d) if os.path.isdir(os.path.join(d, n)))
            if a.limit:
                names = names[:a.limit]
            cases += [(fam, os.path.realpath(os.path.join(d, n))) for n in names]
    if not cases:
        sys.exit("FAIL: no corpus cases found")
    if a.jobs <= 0 or a.chunk <= 0:
        sys.exit("FAIL: jobs and chunk must be positive")
    print(f"cases={len(cases)}", flush=True)
    chunks = [cases[i:i + a.chunk] for i in range(0, len(cases), a.chunk)]
    got3, got3f = {}, {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as ex:
        futs = [(ex.submit(run, os.path.join(BIN, "nearspec-v3-check-d3"), [c for _, c in ch]),
                 ex.submit(run, os.path.join(BIN, "nearspec-v3-check-d3f"), [c for _, c in ch]))
                for ch in chunks]
        for i, (f1, f2) in enumerate(futs):
            got3.update(f1.result())
            got3f.update(f2.result())
            if i % 10 == 0:
                print(f"  {i * a.chunk}/{len(cases)}", flush=True)
    with open(os.path.join(a.out, "d3.jsonl"), "w") as f:
        for k, v in sorted(got3.items()):
            f.write(json.dumps(v) + "\n")
    with open(os.path.join(a.out, "d3f.jsonl"), "w") as f:
        for k, v in sorted(got3f.items()):
            f.write(json.dumps(v) + "\n")
    fam_of = {os.path.normpath(c): fam for fam, c in cases}
    regress, changed, floatmoved, other = [], [], [], []
    for case, fam in fam_of.items():
        g3, g3f = got3.get(case), got3f.get(case)
        mp = os.path.join(case, "meta.json")
        m = json.load(open(mp)) if os.path.exists(mp) else {}
        if g3 is not None:
            r = d3_disagreement(fam, m, g3)
            if r:
                regress.append([case, r, g3.get("reason"), m.get("nearcore")])
        if g3 is not None and g3f is not None and g3.get("verdict") != g3f.get("verdict"):
            changed.append(case)
            viol = m.get("d3_violations") or []
            ok = ("e.float" in viol and g3.get("verdict") == "out_of_domain"
                  and g3f.get("verdict") in ("accept", "reject")
                  and (g3f.get("verdict") == "accept") == bool(m.get("expected_rel")))
            (floatmoved if ok else other).append(
                [case, g3.get("verdict"), g3.get("reason"), g3f.get("verdict"),
                 g3f.get("reason"), m.get("expected_rel"), viol])
    # Independently account for every baseline and successor verdict, including unchanged
    # exclusions. A missing output has already failed in run_batch.
    compare = load_compare()
    metas = {c: json.load(open(os.path.join(c, "meta.json"))) for c in fam_of}
    _, baseline_bad, _, _ = compare.compare("baseline", list(fam_of), metas, got3)
    _, successor_bad, _, _ = compare.compare("floats", list(fam_of), metas, got3f,
                                            domain="successor", widen=["e.float"])
    regress.extend(baseline_bad)
    other.extend(successor_bad)
    v3 = collections.Counter(v.get("verdict") for v in got3.values())
    v3f = collections.Counter(v.get("verdict") for v in got3f.values())
    report = {
        "cases": len(fam_of),
        "verdicts_d3alpha": dict(v3),
        "verdicts_d3f": dict(v3f),
        "d3alpha_regressions": len(regress),
        "d3alpha_regression_samples": regress[:15],
        "verdict_changes": len(changed),
        "float_domain_moves": len(floatmoved),
        "unexpected_moves": len(other),
        "unexpected_move_samples": other[:15],
        "float_move_samples": floatmoved[:10],
    }
    json.dump(report, open(os.path.join(a.out, "report.json"), "w"), indent=1)
    print(json.dumps({k: v for k, v in report.items()
                      if not k.endswith("samples")}, indent=1))
    sys.exit(1 if regress or other else 0)


if __name__ == "__main__":
    main()
