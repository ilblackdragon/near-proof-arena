#!/usr/bin/env python3
"""Bind an `oracle/v3-successor` `fuel-stress`, `eval-time`, `eval-loops` or `code-response` run (W02) to nearcore's outcomes
and to cases.

Input is a run directory produced with `NEAR_SUCCESSOR_SCENARIO=fuel-stress` (or `eval-time`), which contains
`scenario-<chain>.json` (nearcore's outcome tree for every scenario transaction). Each step is
mapped to the honest case that validates the application of its function-call receipt: the
first case of the executor's shard whose height is above the execution height (the witness for
chunk H+1 checks the main transition of chunk H). The step's expectation is checked against
nearcore's recorded status only. Lean's verdict is never an input here.

    collect_fuel_stress.py --source RUN --out MANIFEST.json
"""
import argparse
import collections
import json
from pathlib import Path
import re
import sys

# label suffix -> expected nearcore status class of the function-call receipt
EXPECT = {
    "00.nops-300T": "gas", "01.spin-300T": "gas", "02.blocks200-5T": "gas",
    "03.blocks4999-0.3T": "gas", "04.recurse-300T": "failure", "05.recurse-big-300T": "failure",
    "06.memmax-300T": "gas", "07.memfill-loop-300T": "gas", "08.sha-loop-300T": "gas",
    "09.host-loop-300T": "gas", "10.grow-loop-300T": "gas", "11.count-300T": "value",
    "12.chunk-nops-a": "gas", "13.chunk-nops-b": "gas", "14.chunk-nops-c": "gas",
    "15.blocks200-1T": "gas",
}
# the `eval-time` scenario (W02 arcs): every call runs out of gas
EXPECT_EVAL = {
    "00.blocks4999-300T": "gas", "01.deep4999-300T": "gas", "02.midrun4998-300T": "gas",
    "03.blocks4999-3T": "gas", "04.pushpop4999-3T": "gas", "05.brif4999-3T": "gas",
}
# the `eval-loops` scenario (W02/W16 label memo): every call runs out of gas
EXPECT_LOOPS = {
    "00.pushpop4999-300T": "gas", "01.brif4999-300T": "gas", "02.brtable4999-300T": "gas",
    "03.deepbrif4998-300T": "gas", "04.pushpop4999-3T": "gas", "05.brif4999-3T": "gas",
    "06.brtable4999-3T": "gas", "07.deepbrif4998-3T": "gas", "08.brtablealt4997-300T": "gas",
    "09.brtablealt4997-3T": "gas",
}
# the `code-response` scenario (W02 size limits): every `run` call returns (empty body)
EXPECT_CR = {f"{tag}.{c}": "value" for tag, n, small in (("at64", 16, "crsat"), ("over64", 16, "crsover"),
                                                         ("under64", 8, "crsat"))
             for c in [f"crb{i:02}" for i in range(n)] + [small]}
SCENARIOS = {"FuelStress": ("successor.fuel-stress.", EXPECT), "EvalTime": ("successor.eval-time.", EXPECT_EVAL),
             "EvalLoops": ("successor.eval-loops.", EXPECT_LOOPS),
             "CodeResponse": ("successor.code-response.", EXPECT_CR)}


def index_cases(run):
    by_shard = collections.defaultdict(list)
    for meta_path in sorted(run.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        if meta.get("kind") != "honest":
            continue
        m = re.fullmatch(r"(\d+)-h(\d+)-s(\d+)", meta_path.parent.name)
        if m:
            by_shard[m.group(3)].append((int(m.group(2)), str(meta_path.parent.relative_to(run))))
    for v in by_shard.values():
        v.sort()
    return by_shard


def status_class(st):
    if isinstance(st, dict) and "SuccessValue" in st:
        return "value"
    if isinstance(st, dict):
        return "receipt"
    return "gas" if "GasExceeded" in st or "prepaid gas" in st.lower() else "failure"


def collect(run):
    sc_path = next(run.glob("scenario-*.json"))
    sc = json.loads(sc_path.read_text())
    by_shard = index_cases(run)
    shards = sc["shards"]
    prefix, expect = SCENARIOS[sc["scenario"]]
    rows, problems = [], []
    for x in sc["submitted"]:
        label = x["label"].removeprefix(prefix)
        tree = x["outcomes"]
        fc = next((o for o in tree[1:] if o.get("executed") and o.get("executor") == x["receiver"]), None)
        if fc is None:
            problems.append(f"{label}: function-call receipt not executed")
            continue
        cls = status_class(fc["status"])
        shard = shards[x["receiver"]]
        case = next((rel for h, rel in by_shard.get(shard, []) if h > fc["height"]), None)
        if case is None:
            problems.append(f"{label}: no case after height {fc['height']} on shard {shard}")
        if expect.get(label) != cls:
            problems.append(f"{label}: nearcore status {fc['status']} (expected {expect.get(label)})")
        rows.append(dict(label=label, call=x["call"], height=fc["height"], shard=shard,
                         status=fc["status"], status_class=cls, gas_burnt=fc["gas_burnt"], case=case))
    missing = set(expect) - {r["label"] for r in rows}
    problems += [f"missing step {k}" for k in sorted(missing)]
    return dict(run=str(run), scenario=sc["scenario"], contracts=sc["contracts"], shards=shards,
                steps=rows, problems=problems)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    out = collect(a.source)
    a.out.write_text(json.dumps(out, indent=1) + "\n")
    for p in out["problems"]:
        print("PROBLEM:", p, file=sys.stderr)
    return 1 if out["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
