#!/usr/bin/env python3
"""Audit the declared-profile diagnostic from original D0a witnesses.

Reports failures as evidence instead of dropping fixtures that exceed the profile.
External inputs are read-only; output must be a new directory.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def memory_limit():
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024**3, 16 * 1024**3))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--bin-dir', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--cases', nargs='+', default=[
        '00-h10004-s3', '00-h10006-s3', '00-h10013-s2', '00-h10035-s3'])
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    lane = Path('/data/illia/nearproof-wt/pq-chunk-e2e')
    deps = Path('/data/illia/nearproof-deps/pq-chunk-e2e')
    fixtures = Path('/data/illia/nearproof/oracle/fixtures/v3/public-d0a/d0')
    air = lane/'examples/np-udr-stark-v2/source/near-air-v3.json'
    cert = lane/'research/near-compression/final-soundness/calc/dkt_certs_o2.json'
    excl = lane/'research/near-compression/final-soundness/lean/DKTCertsO2_big.keys'
    dump = deps/'target-classical/release/column-statedump'
    public = deps/'target-classical/release/examples/statepublic'
    prover = a.bin_dir/'declared-profile-prover'
    verifier = a.bin_dir/'local-key-packet-verifier'
    pins = {str(f): sha(f) for f in [air, cert, excl, dump, public, prover, verifier]}
    report = {'status': 'DIAGNOSTIC_LIVE_CORPUS_SCREEN', 'inputs_sha256': pins,
              'memory_limit_bytes': 16 * 1024**3, 'cases': [],
              'limitations': ['D0a only; not full NEAR execution.',
                              'Diagnostic profile; no composed PQ proof or ZK.',
                              'Small sample, not a worst-case size/latency guarantee.']}

    def save():
        (a.output/'audit.json').write_text(json.dumps(report, indent=2)+'\n')

    def run(out, name, argv, cpus='8-15,24-31', positive=True):
        env = dict(os.environ, RAYON_NUM_THREADS='8' if cpus != '8' else '1',
                   NEARPROOF_COMPACT_NSTACK='14')
        argv = list(map(str, argv))
        start = time.monotonic()
        with (out/(name+'.log')).open('wb') as log:
            try:
                result = subprocess.run(['taskset', '-c', cpus, *argv], env=env,
                    stdout=log, stderr=subprocess.STDOUT, timeout=180,
                    preexec_fn=memory_limit)
                code = result.returncode
            except subprocess.TimeoutExpired:
                code = 'timeout'
        return {'command': argv, 'returncode': code,
                'wall_s': time.monotonic()-start,
                'expectation_met': code == 0 if positive else code in (1, 2, 101),
                'log_sha256': sha(out/(name+'.log'))}

    for case in a.cases:
        if Path(case).name != case:
            raise ValueError('case must be a fixture basename')
        fixture = fixtures/case
        out = a.output/case
        out.mkdir()
        row = {'case': case, 'fixture_sha256': {
            name: sha(fixture/name) for name in ['claim.bin', 'witness.bin', 'meta.json']},
            'witness_bytes': (fixture/'witness.bin').stat().st_size, 'stages': {}}
        report['cases'].append(row)
        commands = [('trace', [dump, 'd0a', air, fixture, out/'dump']),
                    ('prove', [prover, air, out/'dump', cert, excl, out/'prove.json']),
                    ('verify', [verifier, 'verify', out/'prove.json.packet', air,
                                fixture/'claim.bin', public, out/'verify.json'])]
        for name, cmd in commands:
            row['stages'][name] = run(out, name, cmd, '8' if name == 'verify' else '8-15,24-31')
            save()
            if not row['stages'][name]['expectation_met']:
                row['failed_stage'] = name
                break
        else:
            proof = json.loads((out/'prove.json').read_text())
            checked = json.loads((out/'verify.json').read_text())
            raw = (out/'prove.json.packet').read_bytes()
            assert raw[:8] == b'NPCHNK02' and len(raw) < 300000
            assert not (out/'prove.json.vk.json').exists()
            assert checked['supplied_key_read'] is False
            assert proof['generated_key_sha384'] == checked['derived_key_sha384']
            row.update(packet_bytes=len(raw), packet_sha256=sha(out/'prove.json.packet'),
                       profile_width=int.from_bytes(raw[8:12], 'little'),
                       key_derived_without_sidecar=True,
                       pipeline_wall_s=sum(s['wall_s'] for s in row['stages'].values()),
                       proof_ready_wall_s=sum(row['stages'][s]['wall_s']
                                              for s in ['trace', 'prove']))
            negatives = {}
            for width in [0, 129, row['profile_width']+1]:
                bad = out/f'width-{width}.packet'
                bad.write_bytes(raw[:8]+width.to_bytes(4, 'little')+raw[12:])
                negatives[str(width)] = run(out, f'reject-width-{width}',
                    [verifier, 'verify', bad, air, fixture/'claim.bin', public,
                     out/f'bad-{width}.json'], '8', False)
            row['negative_widths'] = negatives
            assert all(r['expectation_met'] for r in negatives.values())
        save()
        print(json.dumps({k:v for k,v in row.items() if k not in
                          ['stages','fixture_sha256','negative_widths']}), flush=True)
    report['inputs_unchanged'] = all(sha(f) == h for f,h in pins.items())
    assert report['inputs_unchanged']
    save()


if __name__ == '__main__':
    main()
