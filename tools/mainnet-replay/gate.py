#!/usr/bin/env python3
"""W13 mainnet capture and fail-closed stateless replay gate (see README.md)."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import urllib.request
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'oracle/tools'))
sys.path.insert(0, str(ROOT / 'tools/d3'))
import spec_check_v3 as wire
from replay_successor import run_batch

PIN = '44f7ae6cd7ef08bab604e20a473bf77e35d4c993'
SCHEMA = 'near-mainnet-replay-v1'
ARCHIVE = 'https://mainnet.neardata.xyz/v0/block/{height}'
B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
CHECKS = ['state_root', 'implicit_transition_roots', 'outcome_root',
          'outgoing_receipts_root', 'gas_used', 'gas_limit', 'balance_burnt',
          'validator_proposals', 'congestion_info', 'bandwidth_requests',
          'transaction_root', 'encoded_merkle_root', 'encoded_length',
          'incoming_receipt_proofs', 'applied_receipts_hash']


def digest(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    tmp.replace(path)


def b58(raw):
    n = int.from_bytes(raw, 'big')
    out = ''
    while n:
        n, r = divmod(n, 58)
        out = B58[r] + out
    return '1' * (len(raw) - len(raw.lstrip(b'\0'))) + out


def confined(root, name):
    p = (root / name).resolve()
    if not p.is_relative_to(root.resolve()):
        raise ValueError('path escapes capture directory')
    return p


class ArchiveRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urlsplit(newurl).scheme != 'https':
            raise ValueError('refusing non-HTTPS archive redirect')
        redirected = super().redirect_request(req, fp, code, msg, headers, newurl)
        if redirected and urlsplit(req.full_url).netloc != urlsplit(newurl).netloc:
            redirected.remove_header('Authorization')
        return redirected


def validate_archive_url(url):
    if not url.startswith('https://') or '{height}' not in url:
        raise ValueError('archive must be an HTTPS URL containing {height}')
    parsed = urlsplit(url)
    if parsed.username or parsed.password or parsed.query or parsed.fragment:
        raise ValueError('use a credential-free archive URL; API keys go in an environment variable')


def fetch_block(height, out, url, timeout, api_key_env=None):
    validate_archive_url(url)
    headers = {'User-Agent': 'nearproof-w13/1'}
    if api_key_env:
        key = os.environ.get(api_key_env)
        if not key:
            raise ValueError(f'API-key environment variable is not set: {api_key_env}')
        headers['Authorization'] = 'Bearer ' + key
    req = urllib.request.Request(url.format(height=height), headers=headers)
    with urllib.request.build_opener(ArchiveRedirect()).open(req, timeout=timeout) as r:
        raw = r.read(128 * 1024 * 1024 + 1)
    if len(raw) > 128 * 1024 * 1024:
        raise ValueError('block response exceeds capture limit')
    doc = json.loads(raw)
    block = doc['block']
    if block['header']['height'] != height:
        raise ValueError('archive returned wrong height')
    path = out / 'blocks' / f'{height}.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return block, {'path': str(path.relative_to(out)), 'sha256': digest(path)}


def capture(start, count, out, url=ARCHIVE, timeout=60, api_key_env=None):
    if start < 0 or count <= 0:
        raise ValueError('positive block count and nonnegative height required')
    validate_archive_url(url)
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if (out / 'manifest.json').exists():
        raise ValueError('capture already exists; use a fresh output directory')
    manifest = dict(schema=SCHEMA, chain_id='mainnet', nearcore_commit=PIN,
                    start_height=start, block_count=count, source_url=url, api_key_env=api_key_env,
                    authentication='trusted HTTPS archive; not an independent finality proof',
                    blocks=[], acquisition_errors=[])
    for height in range(start, start + count):
        try:
            block, artifact = fetch_block(height, out, url, timeout, api_key_env)
            manifest['blocks'].append(dict(height=height, artifact=artifact))
        except Exception as exc:
            manifest['acquisition_errors'].append(dict(height=height, error=str(exc)))
        write(out / 'manifest.json', manifest)
    return manifest


def inventory(manifest, root):
    if manifest.get('schema') != SCHEMA or manifest.get('chain_id') != 'mainnet':
        raise ValueError('requires a mainnet W13 capture')
    if manifest.get('nearcore_commit') != PIN:
        raise ValueError('wrong native protocol pin')
    start, count = manifest['start_height'], manifest['block_count']
    if type(start) is not int or type(count) is not int or count <= 0 or start < 0:
        raise ValueError('invalid window')
    blocks, files, entries = {}, {}, []
    for item in manifest['blocks']:
        height = item['height']
        if height in blocks or not start <= height < start + count:
            raise ValueError('duplicate or foreign block height')
        artifact = item['artifact']
        path = confined(root, artifact['path'])
        if digest(path) != artifact['sha256']:
            raise ValueError('block artifact digest mismatch')
        block = json.loads(path.read_text())['block']
        if block['header']['height'] != height:
            raise ValueError('block height mismatch')
        blocks[height] = block
        files[str(path)] = artifact['sha256']
    for height in sorted(blocks):
        block = blocks[height]
        if height - 1 in blocks and block['header']['prev_hash'] != blocks[height-1]['header']['hash']:
            raise ValueError('block chain discontinuity')
        shards = set()
        if not block['chunks']:
            raise ValueError('empty shard population')
        for chunk in block['chunks']:
            sid = chunk['shard_id']
            if sid in shards or chunk['height_included'] > height:
                raise ValueError('duplicate shard or future chunk')
            shards.add(sid)
            entries.append(dict(height=height, shard_id=sid,
                                block_hash=block['header']['hash'], chunk_hash=chunk['chunk_hash'],
                                new_chunk=chunk['height_included'] == height,
                                case_dir=f'cases/h{height}-s{sid}'))
    return blocks, entries, files


def anchor_case(case, entry, blocks):
    """Bind actual claim bytes to the captured on-chain chunk, not to a metadata label."""
    claim = wire.decode_claim((case / 'claim.bin').read_bytes())
    if claim['chain_id'] != b'mainnet' or claim['pv'] != 86:
        raise ValueError('claim is not mainnet PV86')
    inner = wire.decode_inner_bytes(claim['chunk_inner'])
    if b58(inner.chunk_hash) != entry['chunk_hash'] or inner.shard_id != entry['shard_id']:
        raise ValueError('claim chunk commitment differs from mainnet')
    if b58(claim['epoch_id']) != blocks[entry['height']]['header']['epoch_id']:
        raise ValueError('claim epoch differs from mainnet')
    known = {b['header']['hash'] for b in blocks.values()}
    # Context blocks are fetched during attach; their bytes and identity must be checked too.
    context = json.loads((case / 'context-blocks.json').read_text())
    context_hashes = {}
    for item in context:
        p = confined(case, item['path'])
        if digest(p) != item['sha256']:
            raise ValueError('context block digest mismatch')
        block = json.loads(p.read_text())['block']
        known.add(block['header']['hash'])
        context_hashes[str(p)] = item['sha256']
    for block in claim['blocks']:
        if b58(wire.block_hash(block)) not in known:
            raise ValueError('claim segment block not anchored to captured mainnet')
    return context_hashes


def attach(root, source, timeout=60):
    """Import an exported claim/witness pair; capture canonical segment headers independently."""
    root, source = Path(root).resolve(), Path(source).resolve()
    m = json.loads((root / 'manifest.json').read_text())
    blocks, entries, _ = inventory(m, root)
    claim = wire.decode_claim((source / 'claim.bin').read_bytes())
    inner = wire.decode_inner_bytes(claim['chunk_inner'])
    matches = [e for e in entries if e['new_chunk'] and e['chunk_hash'] == b58(inner.chunk_hash)]
    if len(matches) != 1 or claim['chain_id'] != b'mainnet' or claim['pv'] != 86:
        raise ValueError('export does not identify exactly one mainnet PV86 chunk in this capture')
    dest = confined(root, matches[0]['case_dir'])
    if dest.exists():
        raise ValueError('case already attached; refusing overwrite')
    dest.mkdir(parents=True)
    try:
        for name in ('claim.bin', 'witness.bin'):
            shutil.copyfile(source / name, dest / name)
        context = []
        for block in claim['blocks']:
            height = wire.decode_inner_lite(block.lite_raw)['height']
            fetched, artifact = fetch_block(height, dest, m['source_url'], timeout, m.get('api_key_env'))
            if fetched['header']['hash'] != b58(wire.block_hash(block)):
                raise ValueError('export segment differs from mainnet archive')
            context.append(artifact)
        write(dest / 'context-blocks.json', context)
        anchor_case(dest, matches[0], blocks)
    except Exception:
        # Keep failed imports visibly incomplete; no successful import certificate is produced.
        write(dest / 'IMPORT_FAILED.json', {'status': 'failed'})
        raise
    write(dest / 'import.json', {'claim_sha256': digest(dest / 'claim.bin'),
                               'witness_sha256': digest(dest / 'witness.bin')})
    return dest


def pack_witness(raw, code_specs, out):
    """Wrap a raw nearcore Borsh witness plus hash-verified code; no state is synthesized."""
    from struct import pack
    raw, out = Path(raw), Path(out)
    if out.exists():
        raise ValueError('refusing to overwrite witness')
    codes = {}
    for spec in code_specs:
        expected, name = spec.split('=', 1)
        if len(expected) != 64 or digest(name) != expected:
            raise ValueError('contract code SHA256 mismatch')
        codes[expected] = Path(name).read_bytes()
    def vec(data):
        return pack('<I', len(data)) + data
    payload = raw.read_bytes()
    if not payload:
        raise ValueError('empty raw state witness')
    encoded = vec(wire.FORMAT_WITNESS) + vec(payload) + pack('<I', len(codes))
    encoded += b''.join(vec(codes[key]) for key in sorted(codes))
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('xb') as f:
        f.write(encoded)
    return {'raw_sha256': digest(raw), 'witness_sha256': digest(out), 'code_hashes': sorted(codes)}


def native_check(command, case, entry, hashes, timeout):
    """Adapter must execute pinned nearcore against its mainnet store/epoch manager."""
    result = subprocess.run([*command, str(case)], capture_output=True, text=True,
                            timeout=timeout, check=True)
    row = json.loads(result.stdout)
    expected = dict(chain_id='mainnet', nearcore_commit=PIN, block_hash=entry['block_hash'],
                    chunk_hash=entry['chunk_hash'], facts_verified=True, claim_sha256=hashes['claim.bin'],
                    witness_sha256=hashes['witness.bin'])
    if row.get('facts_verified') is not True or any(row.get(k) != v for k, v in expected.items()):
        raise ValueError('native adapter provenance/input binding mismatch')
    if row.get('verdict') not in ('accept', 'reject'):
        raise ValueError('native adapter omitted validator verdict')
    return row


def summarize(rows, expected, captured_blocks, required_blocks, errors):
    counts = Counter(row['status'] for row in rows)
    compared = counts['match'] + counts['mismatch']
    return dict(status='pass' if (not errors and captured_blocks >= required_blocks and expected > 0
                                 and len(rows) == expected and counts['match'] == expected) else 'fail',
                expected_chunks=expected, compared_chunks=compared, counts=dict(counts),
                mismatch_percent=100 * counts['mismatch'] / compared if compared else None,
                mismatch_denominator='matched + mismatched chunks; excludes missing/unsupported/errors',
                replay_coverage_percent=100 * compared / expected if expected else 0,
                verified_match_percent=100 * counts['match'] / expected if expected else 0,
                captured_blocks=captured_blocks, required_blocks=required_blocks, errors=errors)


def replay(root, binary, tier, native_command, out, minimum_blocks=1000, timeout=600):
    root, out = Path(root).resolve(), Path(out).resolve()
    if minimum_blocks < 1000:
        raise ValueError('W13 gate requires at least 1000 blocks; small runs remain diagnostic failures')
    report = dict(schema=SCHEMA, status='fail', comparison='recomputed validator commitments',
                  checked_commitments=CHECKS, independent_finality_verification=False)
    rows, errors, tracked = [], [], {}
    write(out / 'report.json', report | {'status': 'running'})
    try:
        manifest_path = root / 'manifest.json'
        tracked[str(manifest_path)] = digest(manifest_path)
        m = json.loads(manifest_path.read_text())
        blocks, entries, artifacts = inventory(m, root)
        tracked.update(artifacts)
        report['source'] = m.get('source_url')
        report['window'] = {'start': m['start_height'], 'block_count': m['block_count']}
        report['block_capture_percent'] = 100 * len(blocks) / m['block_count']
        report['expected_chunk_count_complete'] = len(blocks) == m['block_count']
        if len(blocks) != m['block_count'] or m.get('acquisition_errors'):
            errors.append('incomplete block capture')
        binary = Path(binary).resolve()
        report['lean'] = dict(path=str(binary), tier=tier)
        if binary.is_file():
            tracked[str(binary)] = digest(binary)
            report['lean']['sha256'] = tracked[str(binary)]
        else:
            errors.append('Lean executable unavailable')
        if native_command:
            exe = Path(shutil.which(native_command[0]) or native_command[0]).resolve()
            tracked[str(exe)] = digest(exe)
            report['native'] = dict(command=native_command, executable_sha256=tracked[str(exe)])
            # Also bind script/config files supplied as command arguments.
            for arg in native_command[1:]:
                if Path(arg).is_file():
                    tracked[str(Path(arg).resolve())] = digest(arg)
        else:
            errors.append('mainnet native validator adapter unavailable')
        expected = [e for e in entries if e['new_chunk']]
        report['missed_chunk_slots'] = len(entries) - len(expected)
        for entry in expected:
            row = dict(entry, status='missing_witness')
            case = confined(root, entry['case_dir'])
            try:
                if not all((case / f).is_file() for f in ('claim.bin', 'witness.bin')):
                    rows.append(row)
                    continue
                if (case / 'IMPORT_FAILED.json').exists():
                    raise ValueError('failed case import')
                hashes = {n: digest(case / n) for n in ('claim.bin', 'witness.bin')}
                tracked.update({str(case / n): h for n, h in hashes.items()})
                tracked[str(case / 'context-blocks.json')] = digest(case / 'context-blocks.json')
                tracked.update(anchor_case(case, entry, blocks))
                row['inputs'] = hashes
                if not native_command or not binary.is_file():
                    row['status'] = 'runner_unavailable'
                else:
                    native = native_check(native_command, case, entry, hashes, timeout)
                    row['native'] = native
                    if native['verdict'] != 'accept':
                        row['status'] = 'native_reject'
                    else:
                        lean = run_batch([str(binary), '--tier', tier], [case], timeout, tier)[str(case)]
                        row['lean'] = lean
                        row['status'] = {'accept': 'match', 'reject': 'mismatch',
                                         'out_of_domain': 'unsupported'}[lean['verdict']]
            except Exception as exc:
                row.update(status='error', error=f'{type(exc).__name__}: {exc}')
            rows.append(row)
            write(out / 'progress.json', summarize(rows, len(expected), len(blocks), minimum_blocks, errors))
        for path, value in tracked.items():
            if digest(path) != value:
                errors.append(f'artifact changed during replay: {path}')
        report.update(summarize(rows, len(expected), len(blocks), minimum_blocks, errors))
    except Exception as exc:
        report.update(summarize(rows, len(rows), 0, minimum_blocks,
                                errors + [f'{type(exc).__name__}: {exc}']))
    report['artifacts'] = tracked
    report['harness_sha256'] = digest(__file__)
    report['results'] = rows
    write(out / 'report.json', report)
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('capture')
    p.add_argument('--start', type=int, required=True)
    p.add_argument('--blocks', type=int, default=1000)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--archive-url', default=ARCHIVE)
    p.add_argument('--api-key-env', help='Environment variable holding a FastNear bearer key (never recorded)')
    p.add_argument('--timeout', type=float, default=60)
    p = sub.add_parser('attach')
    p.add_argument('--capture', type=Path, required=True)
    p.add_argument('--case', type=Path, required=True)
    p = sub.add_parser('pack-witness')
    p.add_argument('--raw', type=Path, required=True)
    p.add_argument('--code', action='append', default=[], help='SHA256=PATH (repeatable)')
    p.add_argument('--out', type=Path, required=True)
    p = sub.add_parser('run')
    p.add_argument('--capture', type=Path, required=True)
    p.add_argument('--binary', type=Path, default=ROOT / 'spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor')
    p.add_argument('--tier', default='curveHosts')
    p.add_argument('--native-command-file', type=Path, help='File containing a JSON argv array')
    p.add_argument('--native-command', help='JSON argv array for mainnet nearcore adapter; case path appended')
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--timeout', type=float, default=600)
    a = ap.parse_args()
    try:
        if a.mode == 'capture':
            m = capture(a.start, a.blocks, a.out, a.archive_url, a.timeout, a.api_key_env)
            print(json.dumps({'captured_blocks': len(m['blocks']), 'errors': m['acquisition_errors']}))
            return 1 if m['acquisition_errors'] else 0
        if a.mode == 'pack-witness':
            print(json.dumps(pack_witness(a.raw, a.code, a.out)))
            return 0
        if a.mode == 'attach':
            print(attach(a.capture, a.case))
            return 0
        if a.native_command and a.native_command_file:
            raise ValueError('choose native-command or native-command-file')
        command_text = a.native_command_file.read_text() if a.native_command_file else a.native_command
        command = json.loads(command_text) if command_text else None
        if command is not None and (not isinstance(command, list) or not command or
                                    not all(isinstance(x, str) and x for x in command)):
            raise ValueError('native command must be a nonempty JSON string array')
        r = replay(a.capture, a.binary, a.tier, command, a.out, timeout=a.timeout)
        pct = r['mismatch_percent']
        print(f"W13 {r['status'].upper()}: mismatch={'N/A (no comparisons)' if pct is None else f'{pct:.4f}%'}; "
              f"coverage={r['replay_coverage_percent']:.4f}%; "
              f"compared={r['compared_chunks']}/{r['expected_chunks']}; {r['counts']}")
        return 0 if r['status'] == 'pass' else 1
    except Exception as exc:
        print(f'W13 ERROR: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
