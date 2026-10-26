#!/usr/bin/env python3
"""Copy the decisive honest chunks of a collected keys-scenario run into a small fixture set.

Per step: the chunk that applies its transaction (transaction-stage result), and the chunk that
executes its first receipt (the action outcome: delegate, host call, gas-key action). Writes
OUT/<case>/{claim.bin,witness.bin,meta.json} and OUT/index.json (origin path, step labels, why,
sha256 of each file). Bytes are copied, never re-encoded.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

FILES = ("claim.bin", "witness.bin", "meta.json")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    a = p.parse_args()
    man = json.loads(a.manifest.read_text())
    paths = {Path(r["case"]).name: Path(r["case"]) for r in man["cases"] if r["kind"] == "honest"}
    pick = {}
    for label, s in sorted(man["steps"].items(), key=lambda kv: kv[1]["step"]):
        if s["applied"]:
            pick.setdefault(s["applied"][0]["case"], []).append((label, "applies_tx"))
        receipts = [o["case"] for o in s["outcome_tree"]
                    if o.get("case") and o["id"] not in s["tx_hashes"]]
        if receipts:
            pick.setdefault(receipts[0], []).append((label, "executes_first_receipt"))
    a.out.mkdir(parents=True, exist_ok=False)
    index = []
    for name in sorted(pick):
        src = paths[name]
        dst = a.out / name
        dst.mkdir()
        for f in FILES:
            shutil.copyfile(src / f, dst / f)
        index.append({"case": name, "origin": str(src), "steps": [{"label": l, "why": w} for l, w in pick[name]],
                      "files": {f: hashlib.sha256((dst / f).read_bytes()).hexdigest() for f in FILES}})
    (a.out / "index.json").write_text(json.dumps(index, indent=1) + "\n")
    print(len(index), "cases")


if __name__ == "__main__":
    main()
