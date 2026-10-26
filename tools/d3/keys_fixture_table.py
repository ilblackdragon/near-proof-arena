#!/usr/bin/env python3
"""Per-step table of a collected keys-scenario run (tools/d3/collect_keys.py manifest) joined with
Lean replay rows (tools/d3/replay_successor.py results.jsonl), one column per Lean results file.

A step's nearcore result is its transaction-stage result in the chunk that applied it, then the
status of every receipt outcome nearcore stored (refunds included, `ok`/failure kind only). Its Lean
cells list the verdict of each selected honest case that carries or executes the step.
"""
import argparse
import collections
import json
import re
from pathlib import Path

INJECTED = {1, 2, 3, 4, 5, 6, 11, 13, 25, 31, 32, 33, 34, 38, 43, 44, 58, 59}


def family(i):
    if i <= 14:
        return "secp256k1 tx key"
    if i <= 22:
        return "secp256k1 delegate"
    if i <= 26:
        return "ML-DSA-65 key"
    if 47 <= i <= 55:
        return "gas-key host"
    return "gas key"


def short(status):
    """`ok`, or nearcore's failure text (`Display`) without the `Failure(Action #i: ` wrapper."""
    if status.startswith("Success"):
        return "ok"
    t = re.sub(r"^Failure\((Action #\d+: )?", "", status).rstrip(")")
    t = re.sub(r"(ed25519|secp256k1):\w+", "<key>", t)
    return t[:70]


def load_lean(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        r = json.loads(line)
        rows[Path(r["case"]).name] = r
    return rows


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--lean", nargs="*", default=[], help="NAME=results.jsonl")
    p.add_argument("--json", type=Path)
    a = p.parse_args()
    man = json.loads(a.manifest.read_text())
    leans = [(x.split("=", 1)[0], load_lean(x.split("=", 1)[1])) for x in a.lean]
    out = []
    print("| # | step | family | mode | nearcore tx | nearcore receipts | " +
          " | ".join(f"Lean {n}" for n, _ in leans) + " |")
    print("|---|---|---|---|---|---|" + "---|" * len(leans))
    for label, s in sorted(man["steps"].items(), key=lambda kv: kv[1]["step"]):
        i = s["step"]
        tx = ",".join(sorted({x["tx_result"] for x in s["applied"]})) or "not applied"
        rec = [short(o["status"]) for o in s["outcome_tree"] if o.get("status") and o["id"] not in s["tx_hashes"]]
        txo = [short(o["status"]) for o in s["outcome_tree"] if o.get("status") and o["id"] in s["tx_hashes"]]
        if any(x != "ok" for x in txo):
            tx += " (" + "; ".join(x for x in txo if x != "ok") + ")"
        cases = sorted(set(s["new_tx_cases"]) | {x["case"] for x in s["applied"]} | set(s["receipt_cases"]))
        cells = []
        for _, rows in leans:
            c = collections.Counter(rows[k]["verdict"] for k in cases if k in rows)
            bad = [f"{k}: {rows[k]['verdict']} ({rows[k]['reason'][:60]})" for k in cases
                   if k in rows and rows[k]["verdict"] != "accept"]
            cells.append(" ".join(f"{v} {n}" for v, n in sorted(c.items())) + ("; " + "; ".join(bad) if bad else ""))
        mode = "inject" if i in INJECTED else "pool"
        print(f"| {i:02} | {s['name']} | {family(i)} | {mode} | {tx} | {'; '.join(rec) or '-'} | " + " | ".join(cells) + " |")
        out.append({"step": i, "name": s["name"], "family": family(i), "mode": mode, "nearcore_tx": tx,
                    "nearcore_receipts": rec, "cases": cases,
                    "lean": {n: {k: rows[k]["verdict"] for k in cases if k in rows} for n, rows in leans}})
    if a.json:
        a.json.write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
