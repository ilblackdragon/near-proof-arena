#!/usr/bin/env python3
"""Blind replay of validator-generated fixture cases (generator corpora, targeted fixtures).

Each case's expected outputs are the `prev_*` fields of the chunk header that nearcore produced and
that the case's witness endorses (`blind_inputs.expected_from_witness`). The case is copied with
every produced value zeroed, the checker runs with `--blind` and emits what it computed, and a case
matches only if every emitted output equals nearcore's. The blinded inputs are also run with
comparisons on as a control, which must not accept.

Only cases whose recorded nearcore verdict is valid are blind-replayed; others are skipped, since a
rejected chunk has no produced outputs to grade. A genesis-main claim is reported separately
(`genesis`): its main outputs are the stored `genesis_chunk_extra`, a claim input by design, so
there is nothing computed to grade beyond the implicit transitions; `--blind` does not run it. `--features` reports, per graded feature, how many
matched cases exercised a non-empty / non-zero value of it.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

import blind_inputs


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def nearcore_valid(meta):
    """The case's recorded nearcore verdict; None when the metadata carries none."""
    if 'nearcore' in meta:
        return meta['nearcore'] == 'ok'
    if 'expected_rel' in meta:
        return bool(meta['expected_rel'])
    return None


def features(expected, facts):
    """Graded features this case exercises with a non-trivial value."""
    c = expected['congestion']
    out = {
        'proposals': bool(expected['proposals']),
        'bandwidth_requests': bool(expected['bwRequests']),
        'congestion_delayed_gas': c['delayedReceiptsGas'] != '0',
        'congestion_buffered_gas': c['bufferedReceiptsGas'] != '0',
        'congestion_receipt_bytes': c['receiptBytes'] != '0',
        'implicit_transitions': facts['implicit_transitions'] > 0,
        'gas_used': expected['gasUsed'] != '0',
        'balance_burnt': expected['balanceBurnt'] != '0',
    }
    return [k for k, v in out.items() if v]


def classify(lean, diffs, control, reason=''):
    if lean == 'out_of_domain' and reason == 'out of domain (c.not_genesis)':
        return 'genesis'
    if lean != 'accept':
        return {'reject': 'mismatch', 'out_of_domain': 'unsupported'}.get(lean, 'error')
    if control == 'accept':
        return 'blind_leak'
    return 'output_mismatch' if diffs else 'match'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--cases', type=Path, required=True,
                   help='file with one case directory per line (relative to --root)')
    p.add_argument('--root', type=Path, default=Path('.'))
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--tier', default='allFeatures')
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--timeout', type=int, default=300)
    p.add_argument('--keep-blinded', action='store_true')
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=False)
    binary = (a.out / 'checker').resolve()
    shutil.copy2(a.binary, binary)
    names = [l.strip() for l in a.cases.read_text().splitlines() if l.strip()]
    if len(set(names)) != len(names):
        raise ValueError('duplicate case')
    blind_root = (a.out / 'blind-cases') if a.keep_blinded else Path(tempfile.mkdtemp(prefix='blind-'))
    inputs = {}
    for n in names:
        for f in ('claim.bin', 'witness.bin', 'meta.json'):
            path = a.root / n / f
            if path.exists():
                inputs[f'{n}/{f}'] = sha(path)
    identities = {'lean_binary_sha256': sha(binary), 'harness_sha256': sha(__file__),
                  'blind_inputs_sha256': sha(blind_inputs.__file__), 'tier': a.tier,
                  'cases_list_sha256': sha(a.cases)}
    (a.out / 'inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')

    def lean_row(case, *mode):
        proc = subprocess.run([str(binary), '--tier', a.tier, *mode, str(case)], capture_output=True,
                              text=True, timeout=a.timeout, check=True)
        lines = proc.stdout.splitlines()
        if len(lines) != 1:
            raise ValueError('expected exactly one result')
        lean = json.loads(lines[0])
        if lean.get('case') != str(case) or lean.get('tier') != a.tier:
            raise ValueError('result identity mismatch')
        if lean.get('verdict') not in ('accept', 'reject', 'out_of_domain'):
            raise ValueError('invalid verdict')
        return lean

    def run(name):
        case = (a.root / name).resolve()
        meta_path = case / 'meta.json'
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
        valid = nearcore_valid(meta)
        if valid is not True:
            return dict(case=name, category='nearcore_reject' if valid is False else 'no_verdict')
        start = time.monotonic()
        blind = blind_root / name.replace('/', '__')
        try:
            expected, facts = blind_inputs.blind_case(case, None, blind)
        except Exception as e:
            return dict(case=name, category='blind_error', error=str(e))
        try:
            lean = lean_row(blind, '--blind')
            control = lean_row(blind)['verdict']
            diffs = blind_inputs.compare_outputs(expected, lean.get('outputs'))
            return dict(case=name, lean=lean, expected=expected, output_diffs=diffs,
                        control_verdict=control, features=features(expected, facts),
                        seconds=time.monotonic() - start, **facts,
                        category=classify(lean['verdict'], diffs, control, lean.get('reason', '')))
        except Exception as e:
            return dict(case=name, category='error', error=str(e), seconds=time.monotonic() - start)
        finally:
            if not a.keep_blinded:
                shutil.rmtree(blind, ignore_errors=True)

    rows = []
    started = time.monotonic()
    with (a.out / 'results.jsonl').open('w') as f, ThreadPoolExecutor(max_workers=a.jobs) as pool:
        for row in pool.map(run, names):
            rows.append(row)
            f.write(json.dumps(row) + '\n')
            f.flush()
            if len(rows) % 200 == 0:
                print(json.dumps({'processed': len(rows), 'total': len(names),
                                  'counts': dict(Counter(r['category'] for r in rows))}), flush=True)
    if not a.keep_blinded:
        shutil.rmtree(blind_root, ignore_errors=True)
    counts = Counter(r['category'] for r in rows)
    changed = [k for k, d in inputs.items() if sha(a.root / k) != d]
    if sha(binary) != identities['lean_binary_sha256']:
        changed.append(str(binary))
    wrong = counts['mismatch'] + counts['output_mismatch'] + counts['blind_leak']
    compared = counts['match'] + wrong
    graded = [r for r in rows if r['category'] not in ('nearcore_reject', 'no_verdict', 'genesis')]
    exercised = Counter(k for r in rows if r['category'] == 'match' for k in r['features'])
    field_diffs = Counter(k for r in rows for k in r.get('output_diffs', []))
    report = dict(
        scope='validator-generated fixtures; expected outputs from the nearcore-produced header',
        cases=len(names), graded=len(graded), counts=dict(counts),
        mismatch_percent=100 * wrong / compared if compared else None,
        verified_match_percent=100 * counts['match'] / len(graded) if graded else None,
        pass_=counts['match'] == len(graded) and not changed and bool(graded),
        matched_cases_exercising=dict(sorted(exercised.items())), field_diffs=dict(field_diffs),
        reasons=dict(Counter(r.get('lean', {}).get('reason', r.get('error', '')) or
                             ','.join(r.get('output_diffs', []))
                             for r in graded if r['category'] != 'match')),
        compared_outputs=list(blind_inputs.COMPARED), identities=identities,
        changed_artifacts=changed, elapsed_seconds=time.monotonic() - started)
    report['pass'] = report.pop('pass_')
    (a.out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))
    return 0 if report['pass'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
