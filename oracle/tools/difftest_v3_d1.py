#!/usr/bin/env python3
"""3-way differential test for near/pv86/chunk-validation/v0, domain D1.

Implementations compared on every case directory (claim.bin, witness.bin, meta.json) of a
corpus written by `near-arena-oracle-v3 gen --domain d1`:
  (1) nearcore oracle — meta.json: nearcore's own validator verdict (`expected_rel`, for
      `tx_valid` mutants with the store's validity answers replaced by the claim's) and the
      oracle's independent Rust D1 predicate (`in_d1`); expected D1 verdict = `expected_rel_d1`;
  (2) Lean   — `nearspec-v3-check-d1` (compiled `NearSpecV3.checkD1`);
  (3) Python — `oracle/tools/spec_check_v3_d1.py` (independent; own Ed25519).
A case agrees iff both checkers accept exactly when expected_rel_d1, and for honest
out-of-domain cases (ood/) both report out_of_domain.

Additionally (`--lean-d0`): the compiled D0 relation on the same corpus — every case it
accepts must be accepted by D1 (InD0 ⊂ InD1 ∧ the relations agree there), and it must accept
exactly when expected_rel_d0.

Coverage: per crafted-transaction class (`tx_labels`) × nearcore's result for that
transaction (`tx_results`), over the honest D1 cases all three accept; per mutant family.

usage: difftest_v3_d1.py --cases DIR --lean EXE --python FILE [--lean-d0] [--jobs N]
         [--report OUT.json]
"""
import argparse, collections, concurrent.futures as cf, json, os, subprocess, sys, time


def run_checker(cmd, dirs, chunk, jobs):
    out = {}
    parts = [dirs[i:i + chunk] for i in range(0, len(dirs), chunk)]

    def one(ds):
        p = subprocess.run(cmd + ds, capture_output=True, text=True, check=True)
        return [json.loads(l) for l in p.stdout.splitlines()]
    with cf.ThreadPoolExecutor(jobs) as ex:
        for res in ex.map(one, parts):
            for j in res:
                out[os.path.normpath(j["case"])] = j
    return out


def family(m):
    parts = m.split(".")
    if parts[0] == "w" and len(parts) > 1 and parts[1] == "drop_node":
        return "w.drop_node." + parts[2]
    return ".".join(parts[:2]) if len(parts) > 1 else m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", required=True)
    ap.add_argument("--lean", required=True)
    ap.add_argument("--python", required=True)
    ap.add_argument("--lean-d0", action="store_true")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--report")
    a = ap.parse_args()
    dirs = []
    for sub in ("d1", "ood", "mutants"):
        p = os.path.join(a.cases, sub)
        if os.path.isdir(p):
            dirs += sorted(os.path.normpath(os.path.join(p, d)) for d in os.listdir(p))
    times, impls = {}, {}
    t = time.time(); impls["lean"] = run_checker([a.lean], dirs, 200, a.jobs); times["lean"] = time.time() - t
    t = time.time(); impls["python"] = run_checker([sys.executable, a.python], dirs, 100, a.jobs)
    times["python"] = time.time() - t
    d0 = None
    if a.lean_d0:
        t = time.time(); d0 = run_checker([a.lean, "--d0"], dirs, 200, a.jobs); times["lean_d0"] = time.time() - t

    stats = collections.Counter()
    disagreements = []
    families = collections.Counter()
    coverage = collections.Counter()
    new_cov = collections.Counter()
    features = collections.Counter()
    d0_issues = []
    for d in dirs:
        meta = json.load(open(os.path.join(d, "meta.json")))
        kind = os.path.basename(os.path.dirname(d))
        exp = meta["expected_rel_d1"]
        stats[f"{kind}.cases"] += 1
        stats[f"{kind}.expected_accept"] += exp
        if kind == "mutants":
            families[(family(meta["mutation"]), exp)] += 1
        ok_all = True
        for name, res in impls.items():
            j = res.get(d)
            if j is None:
                disagreements.append({"case": d, "impl": name, "problem": "missing"}); ok_all = False; continue
            acc = j["verdict"] == "accept"
            ok = acc == exp
            if kind == "ood":
                ok = ok and j["verdict"] == "out_of_domain"
            if not ok:
                ok_all = False
                disagreements.append({"case": d, "impl": name, "expected_rel_d1": exp,
                                      "verdict": j["verdict"], "reason": j["reason"],
                                      "nearcore": meta.get("nearcore"), "mutation": meta.get("mutation")})
        if d0 is not None:
            j0 = d0.get(d)
            acc0 = j0 is not None and j0["verdict"] == "accept"
            if acc0 != meta.get("expected_rel_d0", False):
                d0_issues.append({"case": d, "problem": "D0 verdict != expected_rel_d0", "d0": j0})
            if acc0 and impls["lean"].get(d, {}).get("verdict") != "accept":
                d0_issues.append({"case": d, "problem": "accepted by D0 but not by D1"})
            stats["d0_accepted"] += acc0
        if kind == "d1" and ok_all and exp:
            stats["d1.accepted_by_all"] += 1
            for l, r in zip(meta.get("tx_labels", []), meta.get("tx_results", [])):
                coverage[f"{l} => {r}"] += 1
            for l in meta.get("new_tx_labels", []):
                new_cov[l] += 1
            f = meta.get("features", {})
            ntx = len(meta.get("tx_labels", []))
            features["with_transactions"] += ntx > 0
            features["with_new_transactions"] += len(meta.get("new_tx_labels", [])) > 0
            features["with_failed_tx"] += any(r not in ("success", "success_local") for r in meta.get("tx_results", []))
            features["with_local_receipt"] += "success_local" in meta.get("tx_results", [])
            features["in_d0_too"] += meta.get("in_d0", False)
            features["with_incoming_receipts"] += f.get("n_receipts", 0) > 0
            features["with_implicit_transitions"] += f.get("n_implicit", 0) > 0
            features[f"rs_{f.get('rs')}"] += 1
            features[f"shards_{f.get('n_shards')}"] += 1
    report = {
        "statement": "near/pv86/chunk-validation/v0#D1",
        "corpus": os.path.abspath(a.cases),
        "summary": json.load(open(os.path.join(a.cases, "summary.json"))) if os.path.exists(os.path.join(a.cases, "summary.json")) else None,
        "implementations": {"nearcore": "near-arena-oracle-v3 (meta.json)", "lean": a.lean, "python": a.python},
        "cases": len(dirs), "stats": dict(stats), "seconds": times,
        "disagreements": len(disagreements), "disagreement_samples": disagreements[:50],
        "d0_subset_check": None if d0 is None else {"issues": len(d0_issues), "samples": d0_issues[:20]},
        "tx_coverage_class_x_nearcore_result": dict(sorted(coverage.items())),
        "new_tx_coverage": dict(sorted(new_cov.items())),
        "d1_case_features": dict(sorted(features.items())),
        "mutant_families": {f"{k[0]}|expected={k[1]}": v for k, v in sorted(families.items())},
    }
    s = json.dumps(report, indent=2)
    if a.report:
        open(a.report, "w").write(s + "\n")
    print(json.dumps({k: report[k] for k in ("cases", "stats", "seconds", "disagreements")}, indent=1))
    if d0 is not None:
        print("d0 subset issues:", len(d0_issues))
    for x in disagreements[:20]:
        print(x)
    sys.exit(0 if not disagreements and not d0_issues else 1)


if __name__ == "__main__":
    main()
