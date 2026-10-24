#!/usr/bin/env python3
"""Replay recorded independent float outcomes without nearcore or a WAT assembler."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from replay_successor import REPO, sha256


def main():
    evidence=REPO/'docs/evidence/lean-chunk-completion/float-contracts'
    report=json.loads((evidence/'report.json').read_text())
    results=evidence/'results.jsonl'
    assert report['status']=='pass' and report['cases']==2050 and report['operators']==70
    assert report['results_sha256']==sha256(results), 'oracle evidence digest changed'
    with tempfile.TemporaryDirectory(prefix='float-golden-') as td:
        subprocess.run([sys.executable,str(REPO/'tools/d3/test_float_contracts.py'),
                        '--golden',str(results),'--out',td],check=True,timeout=600)
    dynamic=REPO/'docs/evidence/lean-chunk-completion/float-dynamic-runtime'
    summary=json.loads((dynamic/'report.json').read_text())
    assert summary['status']=='pass' and summary['cases']==32
    assert sha256(dynamic/'results.json')==summary['results_sha256']
    rows=json.loads((dynamic/'results.json').read_text())
    assert len(rows)==32
    binary=REPO/'spec/lean/v3/.lake/build/bin/nearspec-v3-runtime'
    with tempfile.TemporaryDirectory(prefix='float-input-') as td:
        inp=Path(td)/'input.bin'
        for row in rows:
            wasm=dynamic/row['module']['wasm']
            assert sha256(wasm)==row['module']['wasm_sha256']
            inp.write_bytes(bytes.fromhex(row['input']))
            got=subprocess.run([str(binary),str(wasm),'main',str(inp)],
                               capture_output=True,text=True,check=True,timeout=120).stdout.strip()
            assert got==row['oracle'], row['module']
    print('FLOAT GOLDEN PASSED: 2050 operator cases + 32 input-driven bundles')

if __name__=='__main__': main()
