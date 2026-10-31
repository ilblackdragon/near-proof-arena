#!/usr/bin/env python3
"""Verdict tables of the `eth-wallet` fixture family (row L0-D3-006).

Input: the `results.jsonl` of `replay_successor.py` (or `runcheck`-style rows with `case`/`verdict`)
for each tier/binary, and the cases' `meta.json`. Every row is compared with the cold nearcore
verdict recorded by the generator (`expected_rel`); nothing here is a Lean input.

A case is a *wallet case* when its main transition ran code on one of the scenario's magic-hash
ETH-implicit accounts (`executed_contracts` holds an `ethmagic-*` entry on a `0x…` account), or when
it is a mutant of such a chunk. `--control NAME=results.jsonl` adds a breakage-control binary: its
rows are compared with nearcore and with the default binary of the same tier.

Output: JSON with, per tier, the (verdict, nearcore) partition over all / wallet / honest / mutant
cases and per run, the accept-of-a-nearcore-reject count (must be 0), and for each control the rows
that flip against nearcore.
"""
import argparse
import collections
import json
from pathlib import Path


def meta_of(case, cache={}):
    if case not in cache:
        m = json.loads((Path(case) / "meta.json").read_text())
        base = Path(case)
        if m.get("kind") == "mutant":
            # mutants/<base>-<name>: the base honest case's executed contracts decide the stratum
            root = base.parent.parent
            b = next((root / d / m["base"] for d in ("d3", "ood") if (root / d / m["base"]).exists()), None)
            bm = json.loads((b / "meta.json").read_text()) if b else {}
        else:
            bm = m
        wallet = any(str(e.get("name", "")).startswith("ethmagic") and str(e.get("account", "")).startswith("0x")
                     for e in bm.get("executed_contracts", []))
        cache[case] = dict(expected=m["expected_rel"], kind="mutant" if m.get("kind") == "mutant" else "honest",
                           wallet=wallet, run=base.parent.parent.name)
    return cache[case]


def rows(path):
    return {r["case"]: r for r in map(json.loads, Path(path).read_text().splitlines())}


def cell(r, m):
    return f"{r['verdict']}/{'ok' if m['expected'] else 'err'}"


def table(rs):
    out = dict(all=collections.Counter(), wallet=collections.Counter(), honest=collections.Counter(),
               mutant=collections.Counter(), wallet_honest=collections.Counter(), per_run={})
    bad = []
    for c, r in rs.items():
        m = meta_of(c)
        k = cell(r, m)
        out["all"][k] += 1
        out[m["kind"]][k] += 1
        if m["wallet"]:
            out["wallet"][k] += 1
            if m["kind"] == "honest":
                out["wallet_honest"][k] += 1
        out["per_run"].setdefault(m["run"], collections.Counter())[k] += 1
        if (r["verdict"] == "accept") != m["expected"] and r["verdict"] != "out_of_domain":
            bad.append(dict(case=c, verdict=r["verdict"], reason=r.get("reason"), nearcore_ok=m["expected"]))
    res = {k: dict(v) for k, v in out.items() if k != "per_run"}
    res["per_run"] = {k: dict(v) for k, v in sorted(out["per_run"].items())}
    res["disagreements"] = len(bad)
    res["accepts_of_nearcore_rejects"] = sum(1 for b in bad if b["verdict"] == "accept")
    res["disagreement_rows"] = bad[:50]
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--tier", action="append", default=[], metavar="NAME=results.jsonl")
    ap.add_argument("--control", action="append", default=[], metavar="NAME=results.jsonl:BASE_TIER")
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    out = {"tiers": {}, "controls": {}}
    base = {}
    for t in a.tier:
        name, path = t.split("=", 1)
        base[name] = rows(path)
        out["tiers"][name] = table(base[name])
    for t in a.control:
        name, rest = t.split("=", 1)
        path, against = rest.rsplit(":", 1)
        rs = rows(path)
        res = table(rs)
        ref = base[against]
        flips = [c for c, r in rs.items() if c in ref and r["verdict"] != ref[c]["verdict"]]
        res["rows_changed_vs_default"] = len(flips)
        res["changed"] = dict(collections.Counter(f"{ref[c]['verdict']}->{rs[c]['verdict']}/{'ok' if meta_of(c)['expected'] else 'err'}" for c in flips))
        res["changed_reasons"] = dict(collections.Counter((rs[c].get("reason") or "")[:90] for c in flips).most_common(10))
        out["controls"][name] = res
    a.out.write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
    for n, r in list(out["tiers"].items()) + list(out["controls"].items()):
        print(n, json.dumps({k: r[k] for k in ("all", "wallet", "disagreements", "accepts_of_nearcore_rejects")}))


if __name__ == "__main__":
    main()
