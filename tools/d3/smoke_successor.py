#!/usr/bin/env python3
"""Run all seven configurations on the committed smoke fixture and assert widening."""
import json
from pathlib import Path
import tempfile

from replay_successor import REPO, TIERS, replay, run_batch

def main():
    fixture = REPO / "oracle/wasm-d3/tests/d3_smoke/cases"
    entries = json.loads((fixture / "index.json").read_text())["cases"]
    cases = [fixture / e["case_dir"] for e in entries]
    binary = REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor"
    with tempfile.TemporaryDirectory(prefix="successor-smoke-") as tmp:
        for tier in TIERS:
            out = Path(tmp) / tier
            report = replay(binary, tier, cases, out)
            assert report["status"] == "pass", report["disagreements"]
            rows = [json.loads(s) for s in (out / "results.jsonl").read_text().splitlines()]
            for entry, row in zip(entries, rows):
                if "c.not_genesis" in entry["d3_violations"]:
                    expected = "accept" if (tier.startswith("genesis") or tier == "runtimeLimits") else "out_of_domain"
                    assert row["verdict"] == expected, (tier, row)
            print(f"{tier}: {len(cases)} cases; {report['verdicts']}")
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
    print("FLOAT MUTANT SMOKE PASSED: 2 rejects + 2 accepted mutations")
    print("INPUT-DRIVEN FLOAT CHUNK SMOKE PASSED: 8 chunks")
    print("FLOAT CHUNK SMOKE PASSED: 8 chunks, removed-float tier detected")
    print("SUCCESSOR SMOKE PASSED: 35 configuration comparisons, 4 runtime chunks, ablation detected")

if __name__ == "__main__":
    main()
