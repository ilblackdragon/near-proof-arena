#!/usr/bin/env python3
"""Bind an opt-in nearcore curve-hosts scenario run to exact bytes and observed host outcomes.

Every scenario step (`near-arena-oracle-v3-successor curve-steps`) must be executed exactly once in
some honest chunk of the run. A step is located by the executed receipt's method, args hash and
attached gas (unique per step), never by its label. Outcomes are nearcore's recorded execution
status for that receipt: the label says which input class a step was built from, not what nearcore
answered. Selected mutants are those whose base is a selected honest chunk; their verdicts are the
cold nearcore validator's, unchanged.

This collects evidence; it does not assert Lean parity.
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

HOST_FAMILIES = ("alt_bn128", "bls12381", "p256", "ecrecover")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def outcome(status, value_hex):
    """Classify a Debug-printed ExecutionStatus of a curvehosts call.

    Success returns value = result u64 LE ‖ register 1 (src/../contracts/curvehosts.wat `$finish`).
    """
    if value_hex is not None:
        raw = bytes.fromhex(value_hex)
        code = int.from_bytes(raw[:8], "little")
        return {"kind": "return", "code": code, "output_len": len(raw) - 8,
                "value_sha256": hashlib.sha256(raw).hexdigest()}
    m = re.search(r'ExecutionError\("((?:[^"\\]|\\.)*)"\)', status)
    if m:
        msg = m.group(1)
        return {"kind": "error", "message": msg, "class": short_error(msg)}
    return {"kind": "other", "status": status}


def short_error(msg):
    for prefix, name in (("AltBn128 invalid input", "AltBn128InvalidInput"),
                         ("BLS12-381 invalid input", "BLS12381InvalidInput"),
                         ("ECDSA recover error", "ECRecoverError"),
                         ("P256", "P256VerifyInvalidInput"),
                         ("Exceeded the prepaid gas", "GasExceeded"),
                         ("Memory access violation", "MemoryAccessViolation"),
                         ("Integer overflow", "IntegerOverflow")):
        if msg.startswith(prefix):
            return name
    return msg.split(":")[0][:60]


def host_of(label):
    return label.split(".")[3]


def collect(source, steps_path, binary, out, max_mutants):
    steps_doc = json.loads(steps_path.read_text())
    steps = steps_doc["steps"]
    key_of = {}
    for i, s in enumerate(steps):
        k = (s["method"], s["args_sha256"], s["gas"])
        if k in key_of:
            raise ValueError(f"duplicate step key {k}")
        key_of[k] = i
    executed = {}
    selected = {}
    for meta_path in sorted(source.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        if meta.get("kind") != "honest":
            continue
        calls = meta.get("features", {}).get("curve_calls", [])
        if not calls:
            continue
        if type(meta.get("expected_rel")) is not bool:
            raise ValueError(f"missing nearcore verdict: {meta_path}")
        for c in calls:
            k = (c["method"], c["args_sha256"], c["gas"])
            if k not in key_of:
                raise ValueError(f"executed call matches no step: {k} in {meta_path}")
            i = key_of[k]
            if i in executed:
                raise ValueError(f"step {steps[i]['label']} executed twice")
            executed[i] = {"case": meta["case"], "receipt_id": c["receipt_id"],
                           "receiver": c["receiver"], "status": c["status"],
                           "outcome": outcome(c["status"], c.get("value_hex")), "gas_burnt": c["gas_burnt"],
                           "ext_profile": c["ext_profile"]}
        selected[meta["case"]] = (meta_path.parent, meta)
    missing = [steps[i]["label"] for i in range(len(steps)) if i not in executed]
    if missing:
        raise ValueError(f"steps never executed: {missing}")
    # mutants of selected honest chunks: a deterministic, family-balanced subset
    by_family = collections.defaultdict(list)
    for meta_path in sorted(source.glob("mutants/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        if meta.get("base") in selected:
            if type(meta.get("expected_rel")) is not bool:
                raise ValueError(f"missing mutant expectation: {meta_path}")
            fam = re.split(r"[.(]", meta["mutation"])[0]
            by_family[fam].append((meta_path.parent, meta))
    mutants = []
    while len(mutants) < max_mutants and any(by_family.values()):
        for fam in sorted(by_family):
            if by_family[fam] and len(mutants) < max_mutants:
                mutants.append(by_family[fam].pop(0))
    cases_dir = out / "cases"
    if cases_dir.exists():
        shutil.rmtree(cases_dir)
    cases_dir.mkdir(parents=True)
    rows = []
    for kind, items in (("honest", list(selected.values())), ("mutant", mutants)):
        for path, meta in items:
            dst = cases_dir / path.name
            shutil.copytree(path, dst)
            rows.append({"case_dir": f"cases/{path.name}", "kind": kind,
                         "source": str(path.resolve()), "nearcore": meta.get("nearcore"),
                         "expected_rel": meta["expected_rel"],
                         "mutation": meta.get("mutation"), "base": meta.get("base"),
                         "d3_violations": meta.get("d3_violations", []),
                         "files": {n: sha(dst / n) for n in ("claim.bin", "witness.bin", "meta.json")}})
    step_rows = []
    per_host = collections.defaultdict(lambda: collections.Counter())
    for i, s in enumerate(steps):
        e = executed[i]
        o = e["outcome"]
        res = (f"return {o['code']}" if o["kind"] == "return" else
               f"error {o['class']}" if o["kind"] == "error" else "other")
        cls = s["label"].split(".")[4]
        per_host[host_of(s["label"])][f"{cls}: {res}"] += 1
        step_rows.append({"label": s["label"], "method": s["method"], "gas": s["gas"],
                          "args_len": len(s["args_hex"]) // 2, "case_dir": f"cases/{e['case']}",
                          **{k: e[k] for k in ("receipt_id", "receiver", "gas_burnt", "outcome", "ext_profile")}})
    report = {"schema": "near-curve-host-fixtures-v1", "status": "collected",
              "nearcore_pin": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
              "oracle_binary": {"sha256": sha(binary)}, "steps_sha256": sha(steps_path),
              "contract": {k: steps_doc[k] for k in ("contract_hash", "contract_sha256", "contract_len")},
              "collector_sha256": sha(Path(__file__)),
              "population": dict(collections.Counter(r["kind"] for r in rows)),
              "mutant_verdicts": dict(collections.Counter(
                  f"{re.split(r'[.(]', r['mutation'])[0]}: {'accept' if r['expected_rel'] else 'reject'}"
                  for r in rows if r["kind"] == "mutant")),
              "per_host": {h: dict(sorted(c.items())) for h, c in sorted(per_host.items())},
              "steps": step_rows, "cases": rows,
              "limitations": ["labels name the constructed input class, not an expected outcome",
                              "not a Lean differential result"]}
    (out / "manifest.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (out / "cases.txt").write_text("".join(r["case_dir"] + "\n" for r in rows))
    (out / "honest.txt").write_text("".join(r["case_dir"] + "\n" for r in rows if r["kind"] == "honest"))
    (out / "mutants.txt").write_text("".join(r["case_dir"] + "\n" for r in rows if r["kind"] == "mutant"))
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", required=True, type=Path, help="generator --out directory")
    p.add_argument("--steps", required=True, type=Path, help="`curve-steps` output")
    p.add_argument("--binary", required=True, type=Path)
    p.add_argument("--out", required=True, type=Path)
    p.add_argument("--max-mutants", type=int, default=24)
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    try:
        report = collect(a.source, a.steps, a.binary, a.out, a.max_mutants)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print(json.dumps({k: report[k] for k in ("population", "per_host", "mutant_verdicts")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
