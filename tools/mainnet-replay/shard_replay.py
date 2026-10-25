#!/usr/bin/env python3
"""Diagnostic Lean replay of a captured shard against synchronous native export results.

This does not satisfy the all-shard/cold-native W13 gate. Never licenses exclusions.

With `--blind` the checker never receives the values it is graded on: each case is copied with every
produced value zeroed (`blind_inputs.py`), the checker runs with `--blind` and emits what it computed,
and a case matches only if every emitted output equals the canonical mainnet chunk header's value.
As a control, the same blinded inputs are also run with comparisons on, which must not accept.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

import blind_inputs


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def classify_blind(native, lean, diffs, control):
    if native != 'accept':
        return 'native_reject'
    if lean != 'accept':
        return {'reject': 'mismatch', 'out_of_domain': 'unsupported'}.get(lean, 'error')
    if control == 'accept':
        return 'blind_leak'
    return 'output_mismatch' if diffs else 'match'


def classify(native, lean):
    if native != 'accept':
        return 'native_reject'
    return {'accept': 'match', 'reject': 'mismatch', 'out_of_domain': 'unsupported'}.get(lean, 'error')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--captures', type=Path, required=True)
    p.add_argument('--cases', type=Path, required=True)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--native-binary', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--tier', default='allFeatures')
    p.add_argument('--shard', type=int, default=13)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--timeout', type=int, default=120)
    p.add_argument('--blind', action='store_true',
                   help='zero every produced value in the inputs and compare emitted outputs to the chain')
    a = p.parse_args()
    if a.jobs < 1 or a.timeout < 1: p.error('jobs and timeout must be positive')
    a.out.mkdir(parents=True, exist_ok=False)
    binary = (a.out / 'checker').resolve()
    shutil.copy2(a.binary, binary)
    export_rows = json.loads((a.cases / 'exports.json').read_text())
    exports = {}
    for row in export_rows:
        key = str(Path(row['source']).resolve())
        if key in exports: raise ValueError('duplicate native export')
        exports[key] = row
    capture_paths = sorted(a.captures.glob('*/capture.json'))
    if not capture_paths: raise ValueError('empty capture population')
    inputs = {}; expected = []; heights = []
    for path in capture_paths:
        meta = json.loads(path.read_text())
        if meta['shard_id'] != a.shard: continue
        expected.append(path.parent.resolve()); heights.append(meta['block_height'])
        for name in ['capture.json', 'state_witness.borsh', 'block.borsh', 'chunk.borsh']:
            f = path.parent / name; inputs[str(f.resolve())] = sha(f)
    if not expected: raise ValueError('empty requested shard')
    if len(set(heights)) != len(heights): raise ValueError('duplicate captured height')
    for src in expected:
        row = exports.get(str(src), {})
        if row.get('case'):
            case = Path(row['case']).resolve()
            if case != (a.cases / src.name).resolve(): raise ValueError('foreign exported case')
            for name in ['claim.bin', 'witness.bin', 'export.json']:
                f = case / name; inputs[str(f)] = sha(f)
    inputs[str((a.cases / 'exports.json').resolve())] = sha(a.cases / 'exports.json')
    identities = {'lean_binary_sha256': sha(binary), 'native_binary_sha256': sha(a.native_binary),
                  'harness_sha256': sha(__file__), 'blind_inputs_sha256': sha(blind_inputs.__file__),
                  'tier': a.tier, 'mode': 'blind' if a.blind else 'verdict'}
    (a.out / 'inputs.json').write_text(json.dumps(inputs, indent=2)+'\n')

    def lean_row(case, *mode):
        proc = subprocess.run([str(binary), '--tier', a.tier, *mode, str(case)], capture_output=True,
                              text=True, timeout=a.timeout, check=True)
        lines = proc.stdout.splitlines()
        if len(lines) != 1: raise ValueError('expected exactly one result')
        lean = json.loads(lines[0])
        if lean.get('case') != str(case) or lean.get('tier') != a.tier:
            raise ValueError('result identity mismatch')
        if lean.get('verdict') not in ('accept','reject','out_of_domain'):
            raise ValueError('invalid verdict')
        return lean

    def run_blind(src, native):
        case = Path(native['case']).resolve(); start = time.monotonic()
        blind = (a.out / 'blind-cases' / src.name).resolve()
        try:
            expected, facts = blind_inputs.blind_case(case, src, blind)
        except Exception as e:
            return dict(source=str(src), case=str(case), category='blind_error', error=str(e))
        try:
            lean = lean_row(blind, '--blind')
            control = lean_row(blind)['verdict']
            diffs = blind_inputs.compare_outputs(expected, lean.get('outputs'))
            return dict(source=str(src), case=str(case), blind_case=str(blind), native=native,
                        lean=lean, expected=expected, output_diffs=diffs, control_verdict=control,
                        seconds=time.monotonic()-start, **facts,
                        category=classify_blind(native['native_verdict'], lean['verdict'], diffs, control))
        except Exception as e:
            return dict(source=str(src), case=str(case), category='error', error=str(e),
                        seconds=time.monotonic()-start)

    def run(src):
        native = exports.get(str(src))
        if not native or native.get('export_error'):
            return dict(source=str(src), category='missing_case', error=(native or {}).get('export_error'))
        if a.blind:
            return run_blind(src, native)
        case = Path(native['case']).resolve(); start = time.monotonic()
        try:
            proc = subprocess.run([str(binary), '--tier', a.tier, str(case)], capture_output=True,
                                  text=True, timeout=a.timeout, check=True)
            lines = proc.stdout.splitlines()
            if len(lines) != 1: raise ValueError('expected exactly one result')
            lean = json.loads(lines[0])
            if lean.get('case') != str(case) or lean.get('tier') != a.tier:
                raise ValueError('result identity mismatch')
            if lean.get('verdict') not in ('accept','reject','out_of_domain'):
                raise ValueError('invalid verdict')
            return dict(source=str(src), case=str(case), native=native, lean=lean,
                        seconds=time.monotonic()-start,
                        category=classify(native['native_verdict'], lean['verdict']))
        except Exception as e:
            return dict(source=str(src), case=str(case), category='error', error=str(e),
                        seconds=time.monotonic()-start)

    rows=[]; started=time.monotonic()
    with (a.out / 'results.jsonl').open('w') as f, ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for row in pool.map(run, expected):
            rows.append(row);f.write(json.dumps(row)+'\n');f.flush()
            if len(rows)%100 == 0: print(json.dumps({'processed':len(rows),'total':len(expected),'counts':dict(Counter(r['category'] for r in rows))}),flush=True)
    counts=Counter(r['category'] for r in rows)
    changed=[path for path,digest in inputs.items() if not Path(path).exists() or sha(path)!=digest]
    if sha(binary)!=identities['lean_binary_sha256']:changed.append(str(binary))
    if sha(a.native_binary)!=identities['native_binary_sha256']:changed.append(str(a.native_binary))
    wrong=counts['mismatch']+counts['output_mismatch']+counts['blind_leak']
    compared=counts['match']+wrong;n=len(expected)
    report=dict(scope='single-shard diagnostic; not the all-shard W13 gate', shard=a.shard,
        native_cache_policy='fresh transition cache per case; existing node compiled-code cache',
        w13_gate_pass=False, diagnostic_pass=counts['match']==n and not changed,
        expected_chunks=n, counts=dict(counts), mismatch_percent=100*wrong/compared if compared else None,
        replay_coverage_percent=100*compared/n, verified_match_percent=100*counts['match']/n,
        height_range=[min(heights),max(heights)], consecutive_heights=max(heights)-min(heights)+1==n,
        reasons=dict(Counter(r.get('lean',{}).get('reason',r.get('error','')) or ','.join(r.get('output_diffs',[]))
                             for r in rows if r['category']!='match')),
        compared_outputs=list(blind_inputs.COMPARED) if a.blind else None,
        expected_output_source='canonical chunk.borsh header, hash-checked against the captured chunk hash and block' if a.blind else None,
        identities=identities, changed_artifacts=changed, elapsed_seconds=time.monotonic()-started)
    (a.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    return 0 if report['diagnostic_pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
