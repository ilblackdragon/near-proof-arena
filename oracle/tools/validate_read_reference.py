#!/usr/bin/env python3
"""Validate a built D3 read-set reference and run the worker's actual mutators.

Archives digest-named honest proofs, flattened check-local fixtures, per-case
outcomes and strict aggregate counts. Held-out case identifiers are not printed.
Run under the lane's bounded heavy wrapper; --jobs bounds native subprocesses.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time


def sha(data):
    return hashlib.sha256(data).hexdigest()


def run(argv, expected):
    p = subprocess.run([str(a) for a in argv], capture_output=True, timeout=120)
    if p.returncode not in expected:
        raise RuntimeError(f"{Path(argv[0]).name}: exit {p.returncode}, expected {expected}; "
                           f"stderr sha256={sha(p.stderr)}")
    return p.returncode


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--fixtures', type=Path, required=True)
    ap.add_argument('--save', type=Path, required=True)
    ap.add_argument('--mutator', type=Path, required=True)
    ap.add_argument('--jobs', type=int, default=4)
    args = ap.parse_args()
    if not 1 <= args.jobs <= 16:
        ap.error('--jobs must be 1..16')
    candidate, fixtures = args.candidate.resolve(), args.fixtures.resolve()
    save = args.save.resolve()
    save.mkdir(parents=True, exist_ok=False)
    (save / 'honest').mkdir()
    (save / 'negative').mkdir()
    (save / 'fixtures/cases').mkdir(parents=True)
    params = sorted(fixtures.rglob('params.bin'))
    if not params or len({p.read_bytes() for p in params}) != 1:
        raise ValueError('missing or inconsistent fixture parameters')
    shutil.copyfile(params[0], save / 'fixtures/params.bin')
    requests = sorted(fixtures.rglob('request.bin'))
    if not requests:
        raise ValueError('no fixture requests')
    inputs = []
    for index, request in enumerate(requests):
        source = request.parent
        witness = source / 'witness.bin'
        cb, wb = request.read_bytes(), witness.read_bytes()
        positive = (source / 'expected_claim.bin').is_file()
        row = {'index': index, 'positive': positive, 'claim_sha256': sha(cb),
               'witness_sha256': sha(wb), 'witness_bytes': len(wb)}
        if positive:
            expected = (source / 'expected_claim.bin').read_bytes()
            row['expected_claim_sha256'] = sha(expected)
            dest = save / 'fixtures/cases' / f'{index:06d}'
            dest.mkdir()
            for name in ('request.bin', 'witness.bin', 'expected_claim.bin', 'meta.json'):
                if (source / name).is_file():
                    shutil.copyfile(source / name, dest / name)
        inputs.append((source, row))
    positives = sum(row['positive'] for _, row in inputs)
    negatives = len(inputs) - positives
    if not positives or not negatives:
        raise ValueError('require both positive and rejection fixtures')
    provenance = {'candidate_binaries': {name: sha((candidate / 'out' / name).read_bytes())
                                        for name in ('prepare', 'prove', 'verify')},
                  'mutator_sha256': sha(args.mutator.read_bytes()),
                  'driver_sha256': sha(Path(__file__).read_bytes()), 'cases': [r for _, r in inputs],
                  'params_sha256': sha(params[0].read_bytes()), 'jobs': args.jobs}
    (save / 'inputs.json').write_text(json.dumps(provenance, indent=2) + '\n')
    public = save / 'public'
    run([candidate / 'out/prepare', '--params', params[0], '--out', public], {0})
    start = time.monotonic()

    def check_case(item):
        source, row = item
        row = dict(row)
        dest = save / ('honest' if row['positive'] else 'negative') / f"{row['index']:06d}"
        dest.mkdir()
        claim, proof = dest / 'claim.bin', dest / 'proof.bin'
        code = run([candidate / 'out/prove', '--public', public, '--request', source / 'request.bin',
                    '--witness', source / 'witness.bin', '--claim-out', claim, '--proof-out', proof],
                   {0} if row['positive'] else {0, 2, 3})
        row['prove_exit'] = code
        if code == 0:
            cb, pb = claim.read_bytes(), proof.read_bytes()
            if cb != (source / 'request.bin').read_bytes():
                raise ValueError('prover changed the requested claim')
            if row['positive'] and cb != (source / 'expected_claim.bin').read_bytes():
                raise ValueError('honest claim differs from expected claim')
            row['proof_sha256'], row['proof_bytes'] = sha(pb), len(pb)
            row['verify_exit'] = run([candidate / 'out/verify', '--public', public,
                                      '--claim', claim, '--proof', proof], {0} if row['positive'] else {1})
            if row['positive'] and len(pb) > row['witness_bytes']:
                raise ValueError('normalized proof grew')
        if not row['positive']:
            row['raw_verify_exit'] = run([candidate / 'out/verify', '--public', public,
                                          '--claim', source / 'request.bin', '--proof', source / 'witness.bin'], {1})
        return row

    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            results = list(executor.map(check_case, inputs))
        if len(results) != len(inputs) or len({r['index'] for r in results}) != len(inputs):
            raise ValueError('missing or duplicate result rows')
        (save / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
        with (save / 'mutator.log').open('wb') as log:
            subprocess.run([str(args.mutator.resolve()), str(candidate / 'out/verify'), str(public),
                            str(save / 'honest'), str(save / 'mutations'), str(args.jobs)],
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        mutations = json.loads((save / 'mutations/report.json').read_text())
        if mutations['status'] != 'pass' or mutations['honest_cases'] != positives:
            raise ValueError('mutation report incomplete')
        report = {'status': 'pass', 'positive_cases': positives, 'rejection_cases': negatives,
                  'proof_bytes_max': max(r['proof_bytes'] for r in results if r['positive']),
                  'mutations': mutations, 'seconds': time.monotonic() - start,
                  'inputs_sha256': sha((save / 'inputs.json').read_bytes())}
    except Exception as e:
        (save / 'report.json').write_text(json.dumps({'status': 'error', 'error': str(e)}, indent=2) + '\n')
        raise
    (save / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
