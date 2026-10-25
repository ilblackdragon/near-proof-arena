#!/usr/bin/env python3
"""Replay pinned experimental binaries; never infer security from acceptance.

Uses external research inputs read-only. Outputs are confined to --output.
This checks existing executable behavior, not a clean source rebuild.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import struct
import subprocess
import tempfile
import time

NAMES = ['hint', 'column_root', 'frontend', 'stacking', 'endpoint',
         'shared_sumcheck', 'whir']


def digest(path):
    h = hashlib.sha256()
    path = Path(path)
    if path.is_dir():
        for child in sorted(p for p in path.rglob('*') if p.is_file()):
            h.update(child.relative_to(path).as_posix().encode() + b'\0')
            h.update(bytes.fromhex(digest(child)))
        return h.hexdigest()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def sections(raw):
    if len(raw) < 36 or raw[:8] != b'NPCHNK01' or len(raw) > 300000:
        raise ValueError('invalid header/size')
    lengths = struct.unpack('<7I', raw[8:36])
    if 36 + sum(lengths) != len(raw) or min(lengths) == 0 or lengths[1] != 42:
        raise ValueError('invalid sections')
    pos, result = 36, {}
    for name, size in zip(NAMES, lengths):
        result[name] = {'offset': pos, 'bytes': size}
        pos += size
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('--repeats must be positive')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    manifest = json.loads(args.manifest.read_text())
    evidence = manifest['SINGLE_PASS_COMPACT_EVIDENCE.json']
    profiles = evidence['profiles']
    pp = profiles['single-pass-compact-prover']
    vp = profiles['single-pass-independent-verifier']
    pc, vc = pp['command'], vp['command']
    inputs = {p: digest(p) for p in [pc[0], *pc[1:5], vc[0], *vc[3:7]]}
    for profile in [pp, vp]:
        path = profile['command'][0]
        if inputs[path] != profile['executable_sha256']:
            raise ValueError(f'executable drift: {path}; review before repinning')
    # Capture source identity separately: existing binaries are not rebuilt here.
    source_pins = {}
    for path, expected in evidence.get('sources', {}).items():
        if Path(path).is_file():
            actual = digest(path)
            source_pins[path] = {'expected': expected, 'actual': actual,
                                 'matches': actual == expected}
    env = dict(os.environ, RAYON_NUM_THREADS='8')
    rows = []

    def run(name, argv, cpus, positive):
        start = time.monotonic()
        result = subprocess.run(['taskset', '-c', cpus, *argv], env=env,
                                capture_output=True, timeout=180)
        row = {'name': name, 'argv': argv, 'cpus': cpus,
               'wall_s': time.monotonic() - start, 'returncode': result.returncode,
               'stdout_sha256': hashlib.sha256(result.stdout).hexdigest(),
               'stderr_sha256': hashlib.sha256(result.stderr).hexdigest(),
               'expected_acceptance': positive}
        # A crash/signal is not counted as a valid rejection. The current Rust
        # research verifier reports deliberate assertion rejection as exit 101.
        row['expectation_met'] = (result.returncode == 0 if positive
                                  else result.returncode in (1, 2, 101))
        rows.append(row)
        if not row['expectation_met']:
            raise RuntimeError(f'{name}: unexpected exit {result.returncode}')
        return row

    packets = []
    for i in range(args.repeats):
        bench = out / f'prove-{i}.json'
        run(f'prove-{i}', [*pc[:-1], str(bench)], '8-15,24-31', True)
        packet = Path(str(bench) + '.packet')
        layout = sections(packet.read_bytes())
        verify = out / f'verify-{i}.json'
        run(f'verify-{i}', [vc[0], 'verify', str(packet), *vc[3:7], str(verify)], '8', True)
        packets.append({'sha256': digest(packet), 'bytes': packet.stat().st_size,
                        'sections': layout})

    raw = Path(str(out / 'prove-0.json') + '.packet').read_bytes()
    with tempfile.TemporaryDirectory(prefix='tail-mutations-', dir=out) as temp:
        temp = Path(temp)
        cases = {}
        for name, part in sections(raw).items():
            bad = bytearray(raw)
            bad[part['offset'] + part['bytes'] // 2] ^= 1
            cases[name] = bytes(bad)
        cases.update(trailing=raw+b'\x00', truncated=raw[:-1],
                     oversized_length=raw[:8]+b'\xff'*4+raw[12:])
        for name, data in cases.items():
            packet = temp / f'{name}.bin'
            packet.write_bytes(data)
            run(f'reject-{name}', [vc[0], 'verify', str(packet), *vc[3:7],
                                  str(temp / f'{name}.json')], '8', False)

    # Fail on read-only input drift during a run; do not silently mix experiments.
    for path, before in inputs.items():
        if digest(path) != before:
            raise ValueError(f'input changed during audit: {path}')
    report = {'status': 'PREPARED_TRACE_REPLAY_AND_MUTATION_AUDIT',
              'manifest_sha256': digest(args.manifest), 'inputs_sha256': inputs,
              'source_pin_checks': source_pins, 'runs': rows, 'packets': packets,
              'all_packets_identical': len({p['sha256'] for p in packets}) == 1,
              'median_prove_process_s': statistics.median(r['wall_s'] for r in rows
                                                        if r['name'].startswith('prove-')),
              'median_verify_process_s': statistics.median(r['wall_s'] for r in rows
                                                         if r['name'].startswith('verify-')),
              'negative_cases': len(cases),
              'limitations': ['Pinned snapshot binaries rebuilt offline; external path dependencies shared.',
                              'Prepared D0a trace only; execution/trace generation excluded.',
                              'One fixture; no scaling or cross-chunk setup result.',
                              'No concrete PQ composition proof or zero knowledge.',
                              'Negative controls do not establish cryptographic soundness.']}
    (out / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['status', 'median_prove_process_s',
                     'median_verify_process_s', 'negative_cases', 'all_packets_identical']}))


if __name__ == '__main__':
    main()
