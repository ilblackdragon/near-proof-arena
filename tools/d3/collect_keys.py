#!/usr/bin/env python3
"""Bind an opt-in nearcore `keys` or `mldsa` scenario run (oracle/v3-successor/src/keys.rs) to exact bytes.

For every scenario step it records what nearcore did, from two independent sources: the
transaction-stage result in the chunk that applied the transaction (`tx_results` of the honest
case whose `tx_labels` carry the step label) and the step's outcome tree (`keys-outcomes-*.json`,
written by the generator from nearcore's stored execution outcomes, receipts included). A label
alone never establishes an outcome. Selected honest cases are those that carry a step's
transaction (new or applied) or validate the application of one of its receipts (the next chunk
of the executing shard after the block that stored the outcome); selected mutants are the mutants of
selected honest cases. This is a collector, not a Lean differential result.

`--scenario mldsa` selects the `mldsa` step table (labels `successor.mldsa.NN.name`, 47 steps).
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import sys

SCENARIOS = {"keys": ("successor.keys.", 60), "mldsa": ("successor.mldsa.", 47),
             # `mldsa` with NEAR_MLDSA_BOUND_SIGNER: six more steps (z at / one below the norm bound)
             "mldsa-bound": ("successor.mldsa.", 53)}
PREFIX, N_STEPS = SCENARIOS["keys"]
FILES = ("claim.bin", "witness.bin", "meta.json")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def collect(source, binary, scenario="keys"):
    global PREFIX, N_STEPS
    PREFIX, N_STEPS = SCENARIOS[scenario]
    outcomes = {}
    for path in sorted(source.glob("keys-outcomes-*.json")):
        for row in json.loads(path.read_text()):
            outcomes.setdefault(row["label"], []).append(row)
    if not outcomes:
        raise ValueError("no keys-outcomes-*.json (generator run without the keys scenario?)")
    honest = {}
    mutants = []
    for meta_path in sorted(source.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        if type(meta.get("expected_rel")) is not bool:
            raise ValueError(f"missing nearcore verdict: {meta_path}")
        if meta.get("kind") == "honest":
            honest[meta["case"]] = (meta_path.parent, meta)
        else:
            mutants.append((meta_path.parent, meta))
    # An outcome stored at block h comes from applying the chunk included at h; stateless validation
    # checks that application in the witness of the next chunk of the same shard (its main
    # transition). So the honest case that validates an outcome is the first case of that shard
    # above h (a missing chunk in between leaves the transition to the next produced chunk).
    by_shard = collections.defaultdict(list)
    for name in honest:
        m = re.match(r"(\d\d)-h(\d+)-s(\d+)$", name)
        by_shard[(m.group(1), m.group(3))].append((int(m.group(2)), name))
    for v in by_shard.values():
        v.sort()

    def validating_case(height, shard):
        for h, name in by_shard.get(("00", str(shard)), []):
            if h > height:
                return name
        return None

    steps = {}
    selected = {}
    for label in sorted(outcomes):
        m = re.match(re.escape(PREFIX) + r"(\d\d)\.(.+)$", label)
        if not m:
            raise ValueError(f"bad label {label}")
        applied, new, receipt_cases = [], [], []
        for name, (path, meta) in honest.items():
            for i, l in enumerate(meta.get("tx_labels", [])):
                if l == label:
                    applied.append({"case": name, "tx_result": meta.get("tx_results", [None] * (i + 1))[i]})
                    selected[name] = "applies_tx"
            if label in meta.get("new_tx_labels", []):
                new.append(name)
                selected.setdefault(name, "new_tx")
        tree = []
        for row in outcomes[label]:
            for o in row["outcomes"]:
                if o.get("outcome") is None and "status" not in o:
                    tree.append({"id": o["id"], "outcome": None})
                    continue
                case = validating_case(o["block_height"], o["shard_id"])
                present = case is not None
                if present and o["id"] != row["tx_hash"]:
                    receipt_cases.append(case)
                    selected.setdefault(case, "executes_receipt")
                tree.append({k: o[k] for k in ("id", "executor", "status", "block_height", "shard_id")} |
                            {"case": case if present else None})
        steps[label] = {"step": int(m.group(1)), "name": m.group(2),
                        "tx_hashes": [r["tx_hash"] for r in outcomes[label]],
                        "new_tx_cases": sorted(new), "applied": applied,
                        "receipt_cases": sorted(set(receipt_cases)), "outcome_tree": tree}
    missing = [i for i in range(N_STEPS) if not any(v["step"] == i for v in steps.values())]
    unapplied = [l for l, v in steps.items() if not v["applied"] and not v["new_tx_cases"]]
    rows = []
    for name in sorted(selected):
        path, meta = honest[name]
        rows.append({"case": str(path.resolve()), "kind": "honest", "why": selected[name],
                     "expected_rel": meta["expected_rel"], "d3_violations": meta.get("d3_violations", []),
                     "files": {f: sha(path / f) for f in FILES}})
    for path, meta in mutants:
        if meta.get("base") in selected:
            rows.append({"case": str(path.resolve()), "kind": "mutant", "mutation": meta.get("mutation"),
                         "expected_rel": meta["expected_rel"], "verdict_source": meta.get("verdict_source"),
                         "files": {f: sha(path / f) for f in FILES}})
    summary = json.loads((source / "summary.json").read_text())
    return {"schema": "near-keys-fixtures-v1", "status": "collected",
            "nearcore_pin": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
            "source": str(source.resolve()),
            "oracle_binary": {"path": str(binary.resolve()), "sha256": sha(binary)},
            "collector_sha256": sha(Path(__file__)),
            "run": {k: summary.get(k) for k in ("seed", "chains", "honest_witnesses",
                                                 "honest_accepted_by_nearcore", "mutants")},
            "missing_steps": missing, "labels_without_chunk": unapplied,
            "population": dict(collections.Counter(r["kind"] for r in rows)),
            "steps": steps, "cases": rows,
            "limitations": ["a label records what was submitted, not what nearcore did",
                            "outcome trees come from nearcore's stored outcomes, not from Lean",
                            "not a Lean differential result"]}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--binary", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    p.add_argument("--scenario", choices=sorted(SCENARIOS), default="keys")
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    manifest = a.out / "manifest.json"
    manifest.write_text(json.dumps({"status": "collecting"}) + "\n")
    try:
        report = collect(a.source, a.binary, a.scenario)
    except (OSError, ValueError, KeyError, TypeError) as e:
        manifest.write_text(json.dumps({"status": "failed", "error": str(e)}) + "\n")
        print(f"FAIL: {e}", file=sys.stderr)
        return 1
    manifest.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (a.out / "cases.txt").write_text("".join(r["case"] + "\n" for r in report["cases"]))
    (a.out / "honest.txt").write_text("".join(r["case"] + "\n" for r in report["cases"] if r["kind"] == "honest"))
    print(json.dumps({k: report[k] for k in ("status", "population", "missing_steps", "labels_without_chunk")}))
    return 1 if report["missing_steps"] or report["labels_without_chunk"] else 0


if __name__ == "__main__":
    sys.exit(main())
