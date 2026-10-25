#!/usr/bin/env python3
"""Audit source-list membership against native claim-derived roots, not full validity.

The expected root/order manifest must come from the pinned claim-only exporter;
accepting a prover-supplied manifest would eliminate the claimed binding.
"""
import argparse
import hashlib
import json
import struct
from pathlib import Path
from receipt_list_public import emit


def digest(data):
    return hashlib.sha256(data).digest()


def root_from_digest(source_digest, path):
    if len(source_digest) != 32:
        raise ValueError('source digest width')
    acc = digest(source_digest)  # NEAR hashes the 32-byte list item again.
    for step in path:
        sibling = bytes(step['sibling'])
        direction = step['direction']
        if len(sibling) != 32 or type(direction) is not int or direction not in (0, 1):
            raise ValueError('path item')
        acc = digest(sibling + acc if direction == 0 else acc + sibling)
    return acc


def matches(source_digest, path, expected_root):
    try:
        return len(expected_root) == 32 and root_from_digest(source_digest, path) == expected_root
    except (ValueError, TypeError, KeyError):
        return False


def flip(data):
    return bytes([data[0] ^ 1]) + data[1:]


def audit(exports, auth, lists, claims, roots, packet=None, packet_case=None, packet_index=None):
    rows = []
    negatives = 0
    for f in sorted(auth.glob('*.json')):
        a = json.loads(f.read_text())
        case = f.stem
        cb = (claims / case / 'claim.bin').read_bytes()
        wb = (claims / case / 'witness.bin').read_bytes()
        assert digest(cb) == bytes(a['claim_sha256'])
        assert digest(wb) == bytes(a['witness_sha256'])
        messages = json.loads((exports / case / 'sha_r.json').read_text())
        assert len({m['id'] for m in messages}) == len(messages)
        messages = {m['id']: bytes(m['bytes']) for m in messages}
        view = json.loads((exports / case / 'rcpt.json').read_text())
        expected = json.loads((roots / f'{case}.json').read_text())
        assert expected['witness_loaded'] is False
        assert bytes(expected['claim_sha256']) == digest(cb)
        assert expected['own'] == a['own']
        sources = a['sources']
        assert len(expected['sources']) == len(sources)
        for j, (trusted, supplied) in enumerate(zip(expected['sources'], sources)):
            assert trusted['index'] == supplied['index'] == j
            assert trusted['key'] == supplied['key']
            assert trusted['from_shard'] == supplied['expected_from_shard']
            assert trusted['root'] == supplied['expected_root']
        assert len(sources) == len(view['lists'])
        used_keys = {bytes(s['key']) for s in sources}
        # Mirrors the distinct-key count gate; duplicate witness keys resolve last.
        assert len({bytes(k) for k in a['entry_keys']}) == len(sources)
        assert used_keys == {bytes(k) for k in a['entry_keys']}
        for j, source in enumerate(sources):
            assert source['index'] == j
            assert source['from_shard'] == source['expected_from_shard']
            assert source['to_shard'] == a['own'] == view['own']
            raw = messages[1 + 16*j]
            fixture = (lists / f'{case}-list{j}.list').read_bytes()
            count = len(view['lists'][j]['rs'])
            assert source['count'] == count
            assert raw[:12] == struct.pack('<QI', a['own'], count)
            assert len(raw) == source['source_bytes']
            leaf = digest(raw)
            assert leaf == bytes(source['source_sha256']) == fixture[44:76]
            assert fixture[:8] == b'NPLST001'
            assert struct.unpack_from('<QI', fixture, 32) == (a['own'], count)
            root = bytes(source['expected_root'])
            path = source['path']
            assert matches(leaf, path, root)
            assert not matches(flip(leaf), path, root)
            assert not matches(leaf, path, flip(root))
            negatives += 2
            # Omitting the mandatory extra hash must not pass these fixtures.
            wrong = leaf
            for step in path:
                sib = bytes(step['sibling'])
                wrong = digest(sib + wrong if step['direction'] == 0 else wrong + sib)
            assert wrong != root
            negatives += 1
            for i, step in enumerate(path):
                for field, value in [('sibling', list(flip(bytes(step['sibling'])))),
                                     ('direction', 1 - step['direction']), ('direction', 2)]:
                    changed = [dict(x) for x in path]
                    changed[i][field] = value
                    assert not matches(leaf, changed, root)
                    negatives += 1
            rows.append({'case': case, 'index': j, 'count': count, 'depth': len(path),
                         'source_digest': leaf.hex(), 'source_root': root.hex(),
                         'claim_sha256': digest(cb).hex()})
    assert rows
    packet_audit = None
    if packet:
        a = json.loads((auth / f'{packet_case}.json').read_text())
        source = a['sources'][packet_index]
        raw = packet.read_bytes()
        assert raw[:8] == b'NPLIST03'
        cap, mode = struct.unpack_from('<II', raw, 8)
        n = struct.unpack_from('<Q', raw, 16)[0]
        public = raw[24:24+n]
        fixture = (lists / f'{packet_case}-list{packet_index}.list').read_bytes()
        assert public == emit(fixture, cap)
        assert struct.unpack_from('<QQ', public, 24) == (a['own'], source['count'])
        leaf = b''.join(public[i:i+8][::-1] for i in range(40, 72, 8))
        assert leaf == bytes(source['source_sha256'])
        assert matches(leaf, source['path'], bytes(source['expected_root']))
        packet_audit = {'bytes': len(raw), 'sha256': digest(raw).hex(), 'case': packet_case,
                        'source_index': packet_index, 'capacity': cap, 'mode': mode,
                        'depth': len(source['path']), 'source_root': bytes(source['expected_root']).hex(),
                        'cryptographic_proof_verified_by_this_script': False}
    return {'status': 'HOST_SOURCE_MEMBERSHIP_AUDIT_NOT_SUCCINCT_CHUNK_VALIDITY',
            'cases': len({r['case'] for r in rows}), 'lists': len(rows),
            'negative_checks': negatives, 'rows': rows, 'packet': packet_audit,
            'limits': ['Native claim parsing/source-order derivation is trusted in this audit.',
                       'Expected manifest must not be accepted from the prover.',
                       'This script does not verify the lattice proof; use the independent verifier.',
                       'No complete runtime, state, routing, outcomes, history or composed PQ claim.']}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for name in ['exports', 'auth', 'lists', 'claims', 'roots']:
        p.add_argument(name, type=Path)
    p.add_argument('--packet', type=Path)
    p.add_argument('--packet-case')
    p.add_argument('--packet-index', type=int)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    report = audit(a.exports, a.auth, a.lists, a.claims, a.roots, a.packet, a.packet_case, a.packet_index)
    a.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['status', 'cases', 'lists', 'negative_checks', 'packet']}))
