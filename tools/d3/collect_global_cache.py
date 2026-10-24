#!/usr/bin/env python3
"""Bind an opt-in nearcore global/cache scenario to exact bytes and observed coverage.

This selects relevant cases; it does not assert Lean parity or infer action success from a label.
Transaction-stage labels, executed action results and distribution receipt classes remain separate.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect(source, binary, out):
    labels = collections.defaultdict(list)
    action_results = collections.Counter()
    receipt_classes = collections.Counter()
    selected = []
    honest_names = set()
    all_rows = []
    for meta_path in sorted(source.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        all_rows.append((meta_path, meta))
        if meta.get("kind") != "honest":
            continue
        case_labels = [label for key in ("tx_labels", "new_tx_labels")
                       for label in meta.get(key, [])
                       if label.startswith("successor.global-cache.")]
        actions = [result for result in meta.get("action_results", [])
                   if any(word in result for word in ("GlobalContract", "StateInit"))]
        distributions = meta.get("receipt_classes", {}).get("incoming_global_contract", 0)
        if not (case_labels or actions or distributions):
            continue
        if type(meta.get("expected_rel")) is not bool:
            raise ValueError(f"missing nearcore verdict: {meta_path}")
        for label in set(case_labels):
            labels[label].append(str(meta_path.parent))
        action_results.update(actions)
        receipt_classes.update(meta.get("receipt_classes", {}))
        honest_names.add(meta["case"])
        selected.append((meta_path, meta, "honest"))
    missing = [step for step in range(17)
               if not any(label.startswith(f"successor.global-cache.{step:02}.") for label in labels)]
    if missing:
        raise ValueError(f"scenario steps missing from recorded transactions: {missing}")
    for path, meta in all_rows:
        if meta.get("kind") == "honest":
            continue
        # Mutants are named <honest-case>-<mutation>; retain actual oracle metadata unchanged.
        if any(path.parent.name.startswith(name + "-") for name in honest_names):
            if type(meta.get("expected_rel")) is not bool:
                raise ValueError(f"missing mutant expectation: {path}")
            selected.append((path, meta, "mutant"))
    if not selected or not receipt_classes["incoming_global_contract"]:
        raise ValueError("no relevant cases or no observed global-distribution receipt")
    rows = []
    for path, meta, kind in selected:
        rows.append({"case": str(path.parent.resolve()), "kind": kind,
                     "expected_rel": meta["expected_rel"],
                     "d3_violations": meta.get("d3_violations", []),
                     "files": {name: sha(path.parent / name)
                               for name in ("claim.bin", "witness.bin", "meta.json")}})
    report = {"schema": "near-global-cache-fixtures-v1", "status": "collected",
              "nearcore_pin": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
              "oracle_binary": {"path": str(binary.resolve()), "sha256": sha(binary)},
              "collector_sha256": sha(Path(__file__)), "cases": rows,
              "population": dict(collections.Counter(row["kind"] for row in rows)),
              "transaction_labels": dict(labels), "executed_action_results": dict(action_results),
              "receipt_classes": dict(receipt_classes),
              "limitations": ["transaction labels do not establish action success",
                              "raw cold-cache verdicts are not completed-code witness policy verdicts",
                              "not a Lean differential result"]}
    out.mkdir(parents=True, exist_ok=True)
    (out / "manifest.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "cases.txt").write_text("".join(row["case"] + "\n" for row in rows))
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    manifest = args.out / "manifest.json"
    manifest.write_text(json.dumps({"status": "collecting"}) + "\n")
    try:
        report = collect(args.source, args.binary, args.out)
    except (OSError, ValueError, KeyError, TypeError) as error:
        manifest.write_text(json.dumps({"status": "failed", "error": str(error)}) + "\n")
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(json.dumps({key: report[key] for key in ("status", "population", "executed_action_results")}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
