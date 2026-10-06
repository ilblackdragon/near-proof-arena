#!/usr/bin/env python3
"""3-way differential test for near/pv86/chunk-validation/v0, domain D2.

Implementations compared on every case directory (claim.bin, witness.bin, meta.json) of a
corpus written by `near-arena-oracle-v3-d1 gen --domain d2`:
  (1) nearcore oracle — meta.json: nearcore's own validator verdict (`expected_rel`; for
      `tx_valid` mutants with the store's validity answers replaced by the claim's; for the
      `(derived)` trusted-fact mutants the verdict follows from nearcore's semantics, see
      src/d2.rs) and the oracle's independent Rust D2 predicate (`in_d2`); expected D2 verdict
      = `expected_rel_d2`;
  (2) Lean   — `nearspec-v3-check-d2` (compiled checkD2), optional (`--lean`);
  (3) Python — `oracle/tools/spec_check_v3_d2.py` (independent).
A case agrees iff every checker accepts exactly when expected_rel_d2, and for honest
out-of-domain cases (ood/) every checker reports out_of_domain.

D1 ⊂ D2 (`--lean-d1`, needs `nearspec-v3-check-d2 --d1`, and/or `--python-d1 FILE`): the D1
relation on the same corpus — every case it accepts must be accepted by D2, and it must accept
exactly when expected_rel_d1 (mutants: `w.new_tx.drop_rehashed` relabelled as for D1).
`--d1-corpus DIR` additionally runs the D2 checkers on a D1 corpus: every case with
expected_rel_d1 must be accepted by D2, and D1 out-of-domain cases must not be accepted
unless nearcore accepts them.

Coverage (honest D2 cases all checkers accept): crafted / honest transaction label × nearcore
result, action results (receipt source:[actions] => status), receipt classes, queue / epoch
features, mutant families.

usage: difftest_v3_d2.py --cases DIR --python FILE [--lean EXE] [--lean-d1] [--python-d1 FILE]
         [--d1-corpus DIR] [--jobs N] [--report OUT.json]
"""
import argparse, collections, concurrent.futures as cf, json, os, subprocess, sys, time


def run_checker(cmd, dirs, chunk, jobs):
    out = {}
    parts = [dirs[i:i + chunk] for i in range(0, len(dirs), chunk)]

    def one(ds):
        p = subprocess.run(cmd + ds, capture_output=True, text=True)
        if p.returncode != 0:
            sys.stderr.write(p.stderr[-2000:])
        return [json.loads(l) for l in p.stdout.splitlines() if l.startswith('{')]
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


def list_cases(root, subs):
    dirs = []
    for sub in subs:
        p = os.path.join(root, sub)
        if os.path.isdir(p):
            dirs += sorted(os.path.normpath(os.path.join(p, d)) for d in os.listdir(p))
    return dirs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", required=True)
    ap.add_argument("--python", required=True)
    ap.add_argument("--lean")
    ap.add_argument("--lean-d1", action="store_true")
    ap.add_argument("--python-d1")
    ap.add_argument("--d1-corpus")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--report")
    a = ap.parse_args()
    dirs = list_cases(a.cases, ("d2", "ood", "mutants"))
    times, impls = {}, {}
    if a.lean:
        t = time.time(); impls["lean"] = run_checker([a.lean], dirs, 200, a.jobs); times["lean"] = time.time() - t
    t = time.time(); impls["python"] = run_checker([sys.executable, a.python], dirs, 100, a.jobs)
    times["python"] = time.time() - t
    d1runs = {}
    if a.lean and a.lean_d1:
        t = time.time(); d1runs["lean_d1"] = run_checker([a.lean, "--d1"], dirs, 200, a.jobs); times["lean_d1"] = time.time() - t
    if a.python_d1:
        t = time.time(); d1runs["python_d1"] = run_checker([sys.executable, a.python_d1], dirs, 100, a.jobs)
        times["python_d1"] = time.time() - t

    stats = collections.Counter()
    disagreements = []
    families = collections.Counter()
    tx_cov = collections.Counter()
    act_cov = collections.Counter()
    rc_cov = collections.Counter()
    features = collections.Counter()
    ood_fams = collections.Counter()
    d1_issues = []
    for d in dirs:
        meta = json.load(open(os.path.join(d, "meta.json")))
        kind = os.path.basename(os.path.dirname(d))
        exp = meta["expected_rel_d2"]
        stats[f"{kind}.cases"] += 1
        stats[f"{kind}.expected_accept"] += exp
        if kind == "mutants":
            families[(family(meta["mutation"]), exp)] += 1
            stats["mutants.verdict_source." + meta.get("verdict_source", "?")] += 1
        if kind == "ood":
            ood_fams["+".join(meta.get("d2_violations", []))] += 1
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
                disagreements.append({"case": d, "impl": name, "expected_rel_d2": exp,
                                      "verdict": j["verdict"], "reason": j["reason"],
                                      "nearcore": meta.get("nearcore"), "mutation": meta.get("mutation")})
        for name, res in d1runs.items():
            j1 = res.get(d)
            acc1 = j1 is not None and j1["verdict"] == "accept"
            exp1 = meta.get("expected_rel_d1", False)
            if kind == "mutants" and meta.get("mutation") == "w.new_tx.drop_rehashed":
                base = json.load(open(os.path.join(a.cases, "d2", meta["base"], "meta.json")))
                if base.get("d1_violations") == ["w.tx_shape"] and not base.get("tx_labels") \
                        and len(base.get("new_tx_labels", [])) == 1:
                    exp1 = meta["expected_rel_d2"]
            if acc1 != exp1:
                d1_issues.append({"case": d, "impl": name, "problem": "D1 verdict != expected_rel_d1", "d1": j1})
            if acc1 and any(impls[k].get(d, {}).get("verdict") != "accept" for k in impls):
                d1_issues.append({"case": d, "impl": name, "problem": "accepted by D1 but not by D2"})
            stats[f"{name}_accepted"] += acc1
        if kind == "d2" and ok_all and exp:
            stats["d2.accepted_by_all"] += 1
            for l, r in zip(meta.get("tx_labels", []), meta.get("tx_results", [])):
                tx_cov[f"{l} => {r}"] += 1
            for x in meta.get("action_results", []):
                act_cov[x] += 1
            for k, v in meta.get("receipt_classes", {}).items():
                rc_cov[k + ".cases"] += 1
                rc_cov[k + ".receipts"] += v
            f = meta.get("features", {})
            features["in_d1_too"] += meta.get("in_d1", False)
            features["in_d0_too"] += meta.get("in_d0", False)
            features["with_transactions"] += len(meta.get("tx_labels", [])) > 0
            features["with_new_transactions"] += len(meta.get("new_tx_labels", [])) > 0
            features["with_incoming_receipts"] += f.get("n_receipts", 0) > 0
            features["with_implicit_transitions"] += f.get("n_implicit", 0) > 0
            features["multi_epoch_segment"] += f.get("n_epochs", 1) > 1
            features["validator_update_main"] += bool(f.get("validator_update_in_main"))
            features["validator_updates_any"] += f.get("validator_updates", 0) > 0
            features["header_validator_proposals"] += f.get("header_validator_proposals", 0) > 0
            features["header_bandwidth_requests"] += f.get("header_bandwidth_requests", 0) > 0
            features["own_congestion_nonzero_pre"] += bool(f.get("own_congestion_nonzero_pre"))
            features["delayed_queue_nonempty_pre"] += f.get("delayed_queue_pre", 0) > 0
            features["buffers_nonempty_pre"] += f.get("buffered_pre", 0) > 0
            features["yield_queue_nonempty_pre"] += f.get("yield_queue_pre", 0) > 0
            features["pending_data_pre"] += f.get("pending_data_count_pre", 0) > 0
            features["contract_data_removals"] += f.get("contract_data_removals", 0) > 0
            features[f"rs_{f.get('rs')}"] += 1
            features[f"shards_{f.get('n_shards')}"] += 1
    d1c = None
    if a.d1_corpus:
        ddirs = list_cases(a.d1_corpus, ("d1", "ood", "mutants"))
        res = {}
        res["python"] = run_checker([sys.executable, a.python], ddirs, 100, a.jobs)
        if a.lean:
            res["lean"] = run_checker([a.lean], ddirs, 200, a.jobs)
        issues = []
        cnt = collections.Counter()
        for d in ddirs:
            meta = json.load(open(os.path.join(d, "meta.json")))
            e1 = meta.get("expected_rel_d1", False)
            cnt["cases"] += 1
            cnt["expected_rel_d1"] += e1
            for name, r in res.items():
                j = r.get(d)
                v = j["verdict"] if j else "missing"
                if e1 and v != "accept":
                    issues.append({"case": d, "impl": name, "problem": "D1 case not accepted by D2", "verdict": j})
                if v == "accept" and not meta.get("expected_rel", False):
                    issues.append({"case": d, "impl": name, "problem": "D2 accepts a case nearcore rejects", "verdict": j})
                cnt[f"{name}.{v}"] += 1
        d1c = {"corpus": a.d1_corpus, "counts": dict(cnt), "issues": len(issues), "samples": issues[:20]}
    report = {
        "statement": "near/pv86/chunk-validation/v0#D2",
        "corpus": a.cases,
        "summary": json.load(open(os.path.join(a.cases, "summary.json"))) if os.path.exists(os.path.join(a.cases, "summary.json")) else None,
        "implementations": {"nearcore": "near-arena-oracle-v3-d1 --domain d2 (meta.json)", "lean": a.lean, "python": a.python},
        "cases": len(dirs), "stats": dict(stats), "seconds": times,
        "disagreements": len(disagreements), "disagreement_samples": disagreements[:60],
        "d1_subset_check": None if not d1runs else {"issues": len(d1_issues), "samples": d1_issues[:20]},
        "d1_corpus_check": d1c,
        "tx_coverage_label_x_nearcore_result": dict(sorted(tx_cov.items())),
        "action_results": dict(sorted(act_cov.items())),
        "receipt_classes": dict(sorted(rc_cov.items())),
        "d2_case_features": dict(sorted(features.items())),
        "ood_families": dict(sorted(ood_fams.items())),
        "mutant_families": {f"{k[0]}|expected={k[1]}": v for k, v in sorted(families.items())},
    }
    s = json.dumps(report, indent=2)
    if a.report:
        open(a.report, "w").write(s + "\n")
    print(json.dumps({k: report[k] for k in ("cases", "stats", "seconds", "disagreements")}, indent=1))
    if d1runs:
        print("d1 subset issues:", len(d1_issues))
    if d1c:
        print("d1 corpus check:", json.dumps({k: d1c[k] for k in ("counts", "issues")}))
    for x in disagreements[:25]:
        print(x)
    sys.exit(0 if not disagreements and not d1_issues and not (d1c and d1c["issues"]) else 1)


if __name__ == "__main__":
    main()
