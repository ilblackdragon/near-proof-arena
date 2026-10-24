#!/usr/bin/env python3
"""Run all six configurations on the committed smoke fixture and assert widening."""
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
    print("SUCCESSOR SMOKE PASSED: 35 configuration comparisons, 4 runtime chunks, ablation detected")

if __name__ == "__main__":
    main()
