#!/usr/bin/env python3
"""Run all configurations on the committed smoke fixture and assert widening."""
import json
from pathlib import Path
import tempfile

from replay_successor import REPO, TIERS, replay, run_batch
from check_code_witness_policy import check as check_code_policy

def main():
    fixture = REPO / "oracle/wasm-d3/tests/d3_smoke/cases"
    entries = json.loads((fixture / "index.json").read_text())["cases"]
    cases = [fixture / e["case_dir"] for e in entries]
    binary = REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor"
    with tempfile.TemporaryDirectory(prefix="successor-smoke-") as tmp:
        for tier in TIERS:
            out = Path(tmp) / tier
            # Complete-code admission is a stronger relation than the raw cold oracle.
            # Keep the original metadata and check that policy boundary explicitly below.
            compared = [path for entry, path in zip(entries, cases)
                        if tier != "completeCodeGlobal" or "e.code_cache" not in entry["d3_violations"]]
            report = replay(binary, tier, compared, out)
            assert report["status"] == "pass", report["disagreements"]
            rows = [json.loads(s) for s in (out / "results.jsonl").read_text().splitlines()]
            for row in rows:
                entry = next(e for e in entries if (fixture / e["case_dir"]).resolve() == Path(row["case"]))
                if "c.not_genesis" in entry["d3_violations"]:
                    expected = "accept" if (tier.startswith("genesis") or tier in ("runtimeLimits", "storageResolution", "globalActions", "completeCodeGlobal", "curveHosts", "resharding")) else "out_of_domain"
                    assert row["verdict"] == expected, (tier, row)
                # `e.ood_host` is one label covering *both* the curve host family and the
                # state-init / global-contract promise hosts. The curveHosts tier decides the
                # former only, so an e.ood_host case may still be excluded here for a global
                # action. The precise statement this gate can make: a case the tier accepted must
                # not be one it declares out of domain elsewhere, and a curve-only exclusion must
                # now be decided. The second half is asserted on the curve names directly below.
                # The resharding tier also lifts `c.no_resharding`. Its gate is the reverse one: a
                # case carrying only resharding-exclusion labels must be *decided*, never still
                # excluded for resharding. (No fixture in this smoke set carries such a label, so
                # this is a guard against a future regression, not current coverage.)
                if tier == "resharding" and "c.no_resharding" in entry["d3_violations"]:
                    assert row["verdict"] != "out_of_domain" or \
                        "c.same_layout" not in row.get("reason", ""), (tier, row)
                if tier in ("curveHosts", "resharding") and "e.ood_host" in entry["d3_violations"]:
                    reason = row.get("reason", "")
                    glob = "promise_batch_action" in reason or "global" in reason
                    if not glob:
                        # not a global-promise exclusion, so this is a curve/other host: the tier
                        # must have decided it rather than still excluding it
                        assert row["verdict"] != "out_of_domain", (tier, row)
            if tier == "completeCodeGlobal":
                incomplete = [path for entry, path in zip(entries, cases)
                              if "e.code_cache" in entry["d3_violations"]]
                policy = run_batch([str(binary), "--tier", tier], incomplete, 120, tier)
                assert all(r["verdict"] == "reject" and "w.code_complete" in r["reason"]
                           for r in policy.values()), policy
            print(f"{tier}: {len(compared)} raw comparisons; {report['verdicts']}")
    regression = REPO / "docs/evidence/lean-chunk-completion/runtime-chunks-209/cases"
    entries = json.loads((regression / "index.json").read_text())
    cases = [regression / entry["case_dir"] for entry in entries]
    got = run_batch([str(binary), "--tier", "runtimeLimits"], cases, 120, "runtimeLimits")
    assert all(r["verdict"] == "accept" for r in got.values()), got
    broken = run_batch([str(binary), "--tier", "genesisFloatsProtoGas"], cases[:1], 120,
                       "genesisFloatsProtoGas")
    assert next(iter(broken.values()))["verdict"] == "reject", broken
    float_regression = REPO / "docs/evidence/lean-chunk-completion/float-chunks-224/cases"
    float_entries = json.loads((float_regression / "index.json").read_text())
    float_cases = [float_regression / entry["case_dir"] for entry in float_entries]
    assert len(float_cases) == 8
    got = run_batch([str(binary), "--tier", "runtimeLimits"], float_cases, 120, "runtimeLimits")
    assert all(r["verdict"] == "accept" for r in got.values()), got
    removed = run_batch([str(binary), "--tier", "genesis"], float_cases, 120, "genesis")
    assert all(r["verdict"] == "out_of_domain" for r in removed.values()), removed
    dynamic = REPO / "docs/evidence/lean-chunk-completion/float-input-chunks-1284/cases"
    entries = json.loads((dynamic / "index.json").read_text())
    dynamic_cases = [dynamic / entry["case_dir"] for entry in entries]
    assert len(dynamic_cases) == 8
    got = run_batch([str(binary), "--tier", "runtimeLimits"], dynamic_cases, 120, "runtimeLimits")
    assert all(r["verdict"] == "accept" for r in got.values()), got
    mutants = REPO / "docs/evidence/lean-chunk-completion/float-input-mutants-350/cases"
    entries = json.loads((mutants / "index.json").read_text())
    mutant_cases = [mutants / entry["case_dir"] for entry in entries]
    assert len(mutant_cases) == 4
    got = run_batch([str(binary), "--tier", "runtimeLimits"], mutant_cases, 120, "runtimeLimits")
    for entry, path in zip(entries, mutant_cases):
        assert got[str(path.resolve())]["verdict"] == entry["expected"], got
    resolved = REPO / "docs/evidence/lean-chunk-completion/storage-resolution/cases"
    entries = json.loads((resolved / "index.json").read_text())
    resolved_cases = [resolved / entry["case_dir"] for entry in entries]
    assert len(resolved_cases) == 4
    all_cases = cases + float_cases + dynamic_cases + resolved_cases
    got = run_batch([str(binary), "--tier", "storageResolution"], all_cases, 180, "storageResolution")
    assert all(r["verdict"] == "accept" for r in got.values()), got
    removed = run_batch([str(binary), "--tier", "runtimeLimits"], resolved_cases, 120, "runtimeLimits")
    assert all(r["verdict"] == "out_of_domain" for r in removed.values()), removed
    got = run_batch([str(binary), "--tier", "storageResolution"], mutant_cases, 120, "storageResolution")
    for path in mutant_cases:
        meta = json.loads((path / "meta.json").read_text())
        assert got[str(path.resolve())]["verdict"] == ("accept" if meta["expected_rel"] else "reject"), got
    global_root = REPO / "docs/evidence/lean-chunk-completion/global-cache-fixtures/cases"
    global_entries = json.loads((global_root / "index.json").read_text())
    global_cases = [global_root / entry["case_dir"] for entry in global_entries]
    assert len(global_cases) == 28
    promise_root = REPO / "docs/evidence/lean-chunk-completion/global-promise-fixtures/cases"
    promise_cases = [promise_root / name for name in
                     ("caller-success", "caller-gas-failure", "child-action-failure")]
    for tier in ("globalActions", "completeCodeGlobal"):
        got = run_batch([str(binary), "--tier", tier], global_cases + promise_cases, 240, tier)
        exclusions = {
            "00-h10011-s0": "out of domain (w.shape): non-ED25519 transaction key",
            "00-h10021-s2": "out of domain (w.shape): ML-DSA-65 public key",
        }
        for path, row in got.items():
            if Path(path).name in exclusions:
                assert row["verdict"] == "out_of_domain" and row["reason"] == exclusions[Path(path).name], row
            else:
                assert row["verdict"] == "accept", row
    removed = run_batch([str(binary), "--tier", "storageResolution"], promise_cases[:1], 120,
                        "storageResolution")
    assert all(r["verdict"] == "out_of_domain" for r in removed.values()), removed
    with tempfile.TemporaryDirectory(prefix="code-policy-smoke-") as tmp:
        policy = check_code_policy(binary, REPO / "tools/d3/code-policy-fixtures/pairs.json",
                                   Path(tmp), "completeCodeGlobal", 2, 240)
        assert policy["status"] == "pass" and policy["pair_count"] == 5, policy
    print("CODE WITNESS POLICY SMOKE PASSED: 5 pairs, 30 repeated checks")
    print("GLOBAL ACTION SMOKE PASSED: 26 accepted action chunks + 2 key exclusions + 3 promise controls in both tiers; host ablation detected")
    print("STORAGE RESOLUTION SMOKE PASSED: 24 honest chunks + 4 mutants; ETH guard ablation detected")
    print("FLOAT MUTANT SMOKE PASSED: 2 rejects + 2 accepted mutations")
    print("INPUT-DRIVEN FLOAT CHUNK SMOKE PASSED: 8 chunks")
    print("FLOAT CHUNK SMOKE PASSED: 8 chunks, removed-float tier detected")
    print("SUCCESSOR SMOKE PASSED: 49 raw configuration comparisons + 1 complete-code policy check, 4 runtime chunks, ablation detected")

if __name__ == "__main__":
    main()
