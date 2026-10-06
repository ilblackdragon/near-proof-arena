#!/usr/bin/env python3
"""3-way differential test for near/pv86/chunk-validation/v0, domain D0a
(RelD0a = RelD0 ∧ A1 ∧ A2 ∧ Canon0f, spec/near-chunk-validation-v0a.md).

Implementations compared on every case directory (claim.bin, witness.bin, meta.json):
  (1) nearcore oracle  — meta.json written by `near-arena-oracle-v3-d0a gen`: nearcore's own
      validator verdict (`expected_rel`) and the oracle's independent Rust D0 predicate
      (`in_d0a`: ../v3 D0 classifier + src/d0a.rs); expected verdict = `expected_rel_d0a`;
  (2) Lean              — `nearspec-v3-check-d0a` (compiled `NearSpecV3.checkD0a`);
  (3) Python            — `oracle/tools/spec_check_v3_d0a.py` (independent).

A case agrees iff both checkers accept exactly when expected_rel_d0a, and for honest
out-of-domain cases (ood/) and for mutants with `expected_verdict` (constructed
out-of-domain mutants such as the A2 `w.foreign_routed_receipt`) both report that verdict.

usage: difftest_v3.py --cases DIR [--lean EXE] [--python FILE] [--report OUT.json]
         [--lean-jsonl F --python-jsonl F]   (reuse precomputed outputs)
"""
import argparse, collections, json, os, subprocess, sys, time

def run_checker(cmd, dirs, chunk=400):
    out = {}
    for i in range(0, len(dirs), chunk):
        p = subprocess.run(cmd + dirs[i:i + chunk], capture_output=True, text=True, check=True)
        for line in p.stdout.splitlines():
            j = json.loads(line)
            out[os.path.normpath(j["case"])] = j
    return out

def load_jsonl(f):
    return {os.path.normpath(j["case"]): j for j in map(json.loads, open(f))}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", required=True)
    ap.add_argument("--lean")
    ap.add_argument("--python")
    ap.add_argument("--lean-jsonl", nargs="*")
    ap.add_argument("--python-jsonl", nargs="*")
    ap.add_argument("--report")
    a = ap.parse_args()
    dirs = []
    for sub in ("d0", "ood", "mutants"):
        p = os.path.join(a.cases, sub)
        if os.path.isdir(p):
            dirs += sorted(os.path.normpath(os.path.join(p, d)) for d in os.listdir(p))
    impls = {}
    times = {}
    if a.lean_jsonl:
        impls["lean"] = {}
        for f in a.lean_jsonl: impls["lean"].update(load_jsonl(f))
    elif a.lean:
        t = time.time(); impls["lean"] = run_checker([a.lean], dirs); times["lean"] = time.time() - t
    if a.python_jsonl:
        impls["python"] = {}
        for f in a.python_jsonl: impls["python"].update(load_jsonl(f))
    elif a.python:
        t = time.time(); impls["python"] = run_checker([sys.executable, a.python], dirs, 100)
        times["python"] = time.time() - t
    stats = collections.Counter()
    disagreements = []
    families = collections.Counter()
    for d in dirs:
        meta = json.load(open(os.path.join(d, "meta.json")))
        kind = os.path.basename(os.path.dirname(d))
        exp = meta["expected_rel_d0a"]
        stats[f"{kind}.cases"] += 1
        stats[f"{kind}.expected_accept"] += exp
        for viol in meta.get("d0a_violations", []):
            if viol in ("c.gas_limit", "w.proof_routing", "e.sched_canonical", "w.unfolded"):
                stats[f"{kind}.amendment.{viol}"] += 1
        if kind == "mutants":
            families[(meta["mutation"].split(".")[0] + "." + meta["mutation"].split(".")[1] if meta["mutation"].count(".") else meta["mutation"], exp)] += 1
        for name, res in impls.items():
            j = res.get(d)
            if j is None:
                disagreements.append({"case": d, "impl": name, "problem": "missing"}); continue
            acc = j["verdict"] == "accept"
            ok = acc == exp
            if kind == "ood":
                ok = ok and j["verdict"] == "out_of_domain"
            # constructed out-of-domain mutants (e.g. A2 w.proof_routing) pin the exact verdict
            if meta.get("expected_verdict"):
                ok = ok and j["verdict"] == meta["expected_verdict"]
            if not ok:
                disagreements.append({"case": d, "impl": name, "expected_rel_d0a": exp,
                                      "verdict": j["verdict"], "reason": j["reason"],
                                      "nearcore": meta.get("nearcore")})
            stats[f"{kind}.{name}.{j['verdict']}"] += 1
    # A7: the three implementations of unfold_bytes agree exactly (Lean / Python on every case
    # both accept-or-classify-out-of-domain after RelD0; the oracle's on honest accepted cases)
    unfold = {"compared_lean_python": 0, "compared_oracle": 0, "mismatches": [], "values": []}
    for d in dirs:
        meta = json.load(open(os.path.join(d, "meta.json")))
        lu = impls.get("lean", {}).get(d, {}).get("unfold")
        pu = impls.get("python", {}).get(d, {}).get("unfold")
        lv = impls.get("lean", {}).get(d, {}).get("verdict")
        if pu is not None and lv in ("accept", "out_of_domain"):
            unfold["compared_lean_python"] += 1
            if lu != pu:
                unfold["mismatches"].append({"case": d, "lean": lu, "python": pu})
        ou = meta.get("unfold_bytes")
        if ou is not None and pu is not None:
            unfold["compared_oracle"] += 1
            if ou != pu:
                unfold["mismatches"].append({"case": d, "oracle": ou, "python": pu})
        if pu is not None:
            unfold["values"].append(pu)
    vals = sorted(unfold.pop("values"))
    if vals:
        q = lambda f: vals[min(len(vals) - 1, int(f * len(vals)))]
        unfold["distribution"] = {"n": len(vals), "min": vals[0], "p50": q(.5), "p90": q(.9),
                                  "p99": q(.99), "max": vals[-1]}
    unfold["mismatch_count"] = len(unfold["mismatches"])
    disagreements += [{"case": m["case"], "impl": "unfold", "problem": m} for m in unfold["mismatches"]]
    report = {
        "statement": "near/pv86/chunk-validation/v0", "domain": "D0a",
        "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
        "cases_dir": a.cases, "implementations": ["nearcore-oracle"] + list(impls),
        "counts": dict(sorted(stats.items())),
        "mutation_families": {f"{k[0]}|expected_accept={k[1]}": v for k, v in sorted(families.items())},
        "disagreements": len(disagreements), "disagreement_list": disagreements[:200],
        "unfold_bytes": unfold,
        "wall_seconds": times,
    }
    try:
        report["oracle_summary"] = json.load(open(os.path.join(a.cases, "summary.json")))
        report["oracle_summary"].pop("chains", None)
        # amendments on honest witnesses: the oracle's nearcore-based classifier (src/d0a.rs)
        # checks A1, A2 (every receipt of every source proof) and Canon0f on every honest
        # witness with a non-genesis B2
        osum = report["oracle_summary"]
        vc = osum.get("d0_violation_counts", {})
        report["amendments_on_honest_witnesses"] = {
            "honest_witnesses": osum.get("honest_witnesses"),
            **{k: vc.get(k, 0) for k in ("c.gas_limit", "w.proof_routing", "e.sched_canonical", "w.unfolded")},
        }
    except Exception:
        pass
    a2m = [d for d in dirs if os.path.basename(os.path.dirname(d)) == "mutants"
           and d.endswith("w.foreign_routed_receipt")]
    report["a2_foreign_routed_mutants"] = {
        "cases": len(a2m),
        **{f"{name}.out_of_domain": sum(1 for d in a2m if res.get(d, {}).get("verdict") == "out_of_domain")
           for name, res in impls.items()},
    }
    s = json.dumps(report, indent=1, sort_keys=True)
    if a.report:
        open(a.report, "w").write(s + "\n")
    print(json.dumps({k: report.get(k) for k in ("counts", "disagreements", "amendments_on_honest_witnesses", "a2_foreign_routed_mutants", "unfold_bytes")}, indent=1))
    return 0 if not disagreements else 1

if __name__ == "__main__":
    sys.exit(main())
