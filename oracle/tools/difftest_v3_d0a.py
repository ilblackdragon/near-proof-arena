#!/usr/bin/env python3
"""3-way differential test for near/pv86/chunk-validation/v0, domain D0a
(RelD0a = RelD0 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 ∧ A8 ∧ A9 ∧ A10, spec/near-chunk-validation-v0a.md).

Implementations compared on every case directory (claim.bin, witness.bin, meta.json):
  (1) nearcore oracle  — meta.json written by `near-arena-oracle-v3-d0a gen`: nearcore's own
      validator verdict (`expected_rel`) and the oracle's independent Rust D0 predicate
      (`in_d0a`: ../v3 D0 classifier + src/d0a.rs); expected verdict = `expected_rel_d0a`;
  (2) Lean              — `nearspec-v3-check-d0a` (compiled `NearSpecV3.checkD0a`);
  (3) Python            — `oracle/tools/spec_check_v3_d0a.py` (independent).

A case agrees iff both checkers accept exactly when expected_rel_d0a, and for honest
out-of-domain cases (ood/) and for mutants with `expected_verdict` (constructed
out-of-domain mutants such as the A2 `w.foreign_routed_receipt`) both report that verdict;
a mutant with `expected_reason` (the A8 `c.dup_bw_request`: amendment family `c.bw_requests`)
must also name that family in both checkers' reason (Lean reports only its first failing
check, Python all violations joined; such a mutant violates exactly one amendment); the
A10 path-depth mutants `w.path_depth_over` (33 path items) pin `w.path_depth`.

Measured quantities compared exactly across implementations (Lean / Python on every case both
accept or classify out of domain after RelD0; the oracle's on the cases it measured):
`unfold` (A7 unfoldBytes), `chacha_words` (A9 ChaCha20 words drawn by all scheduler runs),
`max_path_depth` (A10 longest used source-proof Merkle path).

usage: difftest_v3.py --cases DIR [--lean EXE] [--python FILE] [--report OUT.json]
         [--lean-jsonl F --python-jsonl F]   (reuse precomputed outputs)
"""
import argparse, collections, json, os, subprocess, sys, time

AMENDMENTS = ("c.gas_limit", "w.proof_routing", "e.sched_canonical", "w.unfolded", "c.bw_requests",
              "e.chacha_words", "w.path_depth")
# measured quantity -> (Lean/Python JSON field, oracle meta.json field)
MEASURES = {"unfold_bytes": ("unfold", "unfold_bytes"),
            "chacha_words": ("chacha_words", "chacha_words"),
            "max_path_depth": ("max_path_depth", "max_path_depth")}


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
            if viol in AMENDMENTS:
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
            if meta.get("expected_reason"):
                ok = ok and meta["expected_reason"] in j["reason"]
            if not ok:
                disagreements.append({"case": d, "impl": name, "expected_rel_d0a": exp,
                                      "verdict": j["verdict"], "reason": j["reason"],
                                      "nearcore": meta.get("nearcore")})
            stats[f"{kind}.{name}.{j['verdict']}"] += 1
    # A7 / A9 / A10: the three implementations of each measured quantity agree exactly (Lean /
    # Python on every case both accept-or-classify-out-of-domain after RelD0; the oracle's on
    # the cases it measured)
    measures = {}
    for mname, (jf, mf) in MEASURES.items():
        m = {"compared_lean_python": 0, "compared_oracle": 0, "mismatches": [], "values": [],
             "values_in_d0a": []}
        for d in dirs:
            meta = json.load(open(os.path.join(d, "meta.json")))
            lj = impls.get("lean", {}).get(d, {})
            pj = impls.get("python", {}).get(d, {})
            lu, pu, lv = lj.get(jf), pj.get(jf), lj.get("verdict")
            if pu is not None and lv in ("accept", "out_of_domain"):
                m["compared_lean_python"] += 1
                if lu != pu:
                    m["mismatches"].append({"case": d, "lean": lu, "python": pu})
            ou = meta.get(mf)
            if ou is not None and pu is not None:
                m["compared_oracle"] += 1
                if ou != pu:
                    m["mismatches"].append({"case": d, "oracle": ou, "python": pu})
            if pu is not None:
                m["values"].append(pu)
                if lv == "accept":
                    m["values_in_d0a"].append(pu)
        for key in ("values", "values_in_d0a"):
            vals = sorted(m.pop(key))
            if vals:
                q = lambda f, vals=vals: vals[min(len(vals) - 1, int(f * len(vals)))]
                m["distribution" if key == "values" else "distribution_in_d0a"] = {
                    "n": len(vals), "min": vals[0], "p50": q(.5), "p90": q(.9), "p99": q(.99),
                    "max": vals[-1], "nonzero": sum(1 for x in vals if x)}
        m["mismatch_count"] = len(m["mismatches"])
        disagreements += [{"case": x["case"], "impl": mname, "problem": x} for x in m["mismatches"]]
        measures[mname] = m
    unfold = measures["unfold_bytes"]
    report = {
        "statement": "near/pv86/chunk-validation/v0", "domain": "D0a",
        "nearcore_commit": "44f7ae6cd7ef08bab604e20a473bf77e35d4c993",
        "cases_dir": a.cases, "implementations": ["nearcore-oracle"] + list(impls),
        "counts": dict(sorted(stats.items())),
        "mutation_families": {f"{k[0]}|expected_accept={k[1]}": v for k, v in sorted(families.items())},
        "disagreements": len(disagreements), "disagreement_list": disagreements[:200],
        "unfold_bytes": unfold,
        "chacha_words": measures["chacha_words"],
        "max_path_depth": measures["max_path_depth"],
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
            **{k: vc.get(k, 0) for k in AMENDMENTS},
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
    a8m = [d for d in dirs if os.path.basename(os.path.dirname(d)) == "mutants"
           and d.endswith("c.dup_bw_request")]
    report["a8_dup_bw_request_mutants"] = {
        "cases": len(a8m),
        **{f"{name}.out_of_domain_c.bw_requests": sum(
            1 for d in a8m if res.get(d, {}).get("verdict") == "out_of_domain"
            and "c.bw_requests" in res.get(d, {}).get("reason", ""))
           for name, res in impls.items()},
    }
    # A8 on everything else: no checker reports c.bw_requests outside the A8 mutants
    a8set = set(a8m)
    report["a8_reported_elsewhere"] = {
        name: sum(1 for d in dirs if d not in a8set and "c.bw_requests" in res.get(d, {}).get("reason", ""))
        for name, res in impls.items()}
    # A10 path-depth mutants: exactly at the bound (in D0a iff the base case is) and one above
    pd = {}
    for mut, want in (("w.path_depth_at_bound", None), ("w.path_depth_over", "out_of_domain")):
        ms = [d for d in dirs if os.path.basename(os.path.dirname(d)) == "mutants" and d.endswith(mut)]
        row = {"cases": len(ms),
               "nearcore_accepts": sum(1 for d in ms if json.load(open(os.path.join(d, "meta.json"))).get("expected_rel"))}
        for name, res in impls.items():
            row[f"{name}.accept"] = sum(1 for d in ms if res.get(d, {}).get("verdict") == "accept")
            row[f"{name}.out_of_domain_w.path_depth"] = sum(
                1 for d in ms if res.get(d, {}).get("verdict") == "out_of_domain"
                and "w.path_depth" in res.get(d, {}).get("reason", ""))
        pd[mut] = row
    report["a10_path_depth_mutants"] = pd
    pdset = {d for d in dirs if d.endswith("w.path_depth_over")}
    report["a10_reported_elsewhere"] = {
        name: sum(1 for d in dirs if d not in pdset and "w.path_depth" in res.get(d, {}).get("reason", ""))
        for name, res in impls.items()}
    report["a9_reported"] = {
        name: sum(1 for d in dirs if "e.chacha_words" in res.get(d, {}).get("reason", ""))
        for name, res in impls.items()}
    s = json.dumps(report, indent=1, sort_keys=True)
    if a.report:
        open(a.report, "w").write(s + "\n")
    print(json.dumps({k: report.get(k) for k in ("counts", "disagreements", "amendments_on_honest_witnesses", "a2_foreign_routed_mutants", "a8_dup_bw_request_mutants", "a8_reported_elsewhere", "a10_path_depth_mutants", "a10_reported_elsewhere", "a9_reported", "unfold_bytes", "chacha_words", "max_path_depth")}, indent=1))
    return 0 if not disagreements else 1

if __name__ == "__main__":
    sys.exit(main())
