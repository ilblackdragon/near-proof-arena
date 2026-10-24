#!/usr/bin/env python3
"""Corpus-free CI replay of generated modules against recorded pinned-nearcore outputs."""
import json
import re
from pathlib import Path
import subprocess
import tempfile

from replay_successor import REPO, sha256
from test_runtime_limits import module
import hashlib

def main():
    evidence = REPO / "docs/evidence/lean-chunk-completion/runtime-limits"
    report = json.loads((evidence / "report.json").read_text())
    results = evidence / "results.jsonl"
    assert report["pass"] and report["compared"] == report["requested"] == 1030
    assert sha256(results) == report["results_sha256"], "golden output digest mismatch"
    rows = [json.loads(line) for line in results.read_text().splitlines()]
    assert len(rows) == 1030 and len({r["index"] for r in rows}) == 1030
    binary = REPO / "spec/lean/v3/.lake/build/bin/nearspec-v3-runtime"
    with tempfile.TemporaryDirectory(prefix="runtime-golden-") as tmp:
        path = Path(tmp) / "module.wasm"
        for row in rows:
            code = module(**row["parameters"])
            assert hashlib.sha256(code).hexdigest() == row["input_sha256"], "generator drift"
            path.write_bytes(code)
            got = subprocess.run([str(binary), str(path)],text=True,capture_output=True,
                                 timeout=60,check=True).stdout.strip()
            assert got == row["nearcore"], (row["index"], row["parameters"], got, row["nearcore"])
        phases = json.loads((evidence / "phase-cases.json").read_text())
        assert len(phases) == 6
        for row in phases:
            code = module(row["globals"], **row["parameters"])
            assert hashlib.sha256(code).hexdigest() == row["wasm_sha256"]
            path.write_bytes(code)
            got = subprocess.run([str(binary), str(path)], text=True, capture_output=True,
                                 timeout=60, check=True).stdout.strip()
            # Existing relation quotients LinkError message text, not gas or phase.
            norm = lambda s: re.sub(r'LinkError \{ msg: .*? \}', 'LinkError', s)
            assert norm(got) == norm(row["oracle"]), (row, got)
        path.write_bytes(module(66000))
        broken = subprocess.run([str(binary),str(path),"main","--ablate-loading-limits"],
                                text=True,capture_output=True,timeout=60,check=True).stdout.strip()
        assert broken.startswith("ok "), "loading-check ablation no longer reproduces the defect"
    print("RUNTIME GOLDEN PASSED: 1030 allocation cases + 6 phase cases; removed-check control detected")

if __name__ == "__main__":
    main()
