#!/usr/bin/env python3
"""Host audit: per-account trie path witnesses must hash-chain to the claim's
prev_state_root, and the leaf value must equal the account table's initial bytes.

Chain semantics (native PTrie.node_ser / hash_of):
- Leaf:   0 || u32le(len(hexPrefix)) || hexPrefix || value_ref || u64le(mem)
          hash = sha256(ser)
- Ext:    3 || u32le(len(hexPrefix)) || hexPrefix || child_hash || u64le(mem)
- Branch: 1|2 (value slot) || u16le(kids bitmap) || child hashes* || u64le(mem)

The FIRST node serialization in each witness must hash to the claim's
prev_state_root. Each subsequent node's hash is embedded in its parent, and
the LEAF's embedded value_ref must be len||sha256(initial account bytes) with
len=72. This is a host check on exported witnesses, NOT a circuit proof.
"""
import argparse
import hashlib
import json
import struct
from pathlib import Path


def u32le(x):
    return struct.pack('<I', x)


def u16le(x):
    return struct.pack('<H', x)


def u64le(x):
    return struct.pack('<Q', x)


def parse_node(ser, mem_end):
    """Parse one node serialization; return (kind, fields) for verification."""
    tag = ser[0]
    if tag == 0:  # Leaf
        hplen = struct.unpack_from('<I', ser, 1)[0]
        hp = ser[5:5+hplen]
        assert len(hp) == hplen
        value_ref = ser[5+hplen:5+hplen+36]
        mem = struct.unpack_from('<Q', ser, 5+hplen+36)[0]
        assert 5+hplen+36+8 == len(ser)
        return ('leaf', hp, value_ref, mem)
    if tag == 3:  # Ext
        hplen = struct.unpack_from('<I', ser, 1)[0]
        hp = ser[5:5+hplen]
        child = ser[5+hplen:5+hplen+32]
        mem = struct.unpack_from('<Q', ser, 5+hplen+32)[0]
        assert 5+hplen+32+8 == len(ser)
        return ('ext', hp, child, mem)
    if tag in (1, 2):  # Branch (1 = no value, 2 = inline value)
        pos = 1
        value_ref = None
        if tag == 2:
            value_ref = ser[1:37]
            pos = 37
        bitmap = struct.unpack_from('<H', ser, pos)[0]
        pos += 2
        kids = bin(bitmap).count('1')
        children = []
        for _ in range(kids):
            children.append(ser[pos:pos+32])
            pos += 32
        mem = struct.unpack_from('<Q', ser, pos)[0]
        pos += 8
        assert pos == len(ser)
        return ('branch', value_ref, children, mem)
    raise ValueError(f'unknown node tag {tag}')


def check(paths_json, ledger_fixture):
    paths = json.loads(Path(paths_json).read_text())
    fixture = Path(ledger_fixture).read_bytes()
    assert fixture[:9] == b'NPMLEDG01'
    pre_state_root = fixture[9:41]
    assert bytes(paths['pre_state_root']) == pre_state_root, 'pre_state_root mismatch with fixture'
    accounts = {}
    off = 41
    for _ in range(16):
        row = fixture[off:off+224]
        active = struct.unpack_from('<Q', row, 0)[0]
        if active:
            name_len = struct.unpack_from('<Q', row, 8)[0]
            name = row[16:16+name_len]
            initial = row[80:80+72]
            accounts[name] = initial
        off += 224
    assert len(accounts) == len(paths['accounts']), 'account count mismatch'
    for entry in paths['accounts']:
        name = bytes(entry['receiver'])
        chain = [bytes(x) for x in entry['node_serializations']]
        assert name in accounts, f'witness for unknown account {name!r}'
        # Hash-chain: root node hashes to the claim root; each deeper node's
        # hash is embedded in its parent; the deepest node is the leaf.
        node_hash = hashlib.sha256(chain[0]).digest()
        assert node_hash == pre_state_root, f'root chain mismatch for {name!r}'
        for parent, child in zip(chain, chain[1:]):
            kind, *fields = parse_node(parent, None)
            child_hash = hashlib.sha256(child).digest()
            if kind == 'ext':
                hp, embedded, _mem = fields
                assert embedded == child_hash, f'ext child hash mismatch for {name!r}'
            elif kind == 'branch':
                value_ref, children, _mem = fields
                assert child_hash in children, f'branch child hash missing for {name!r}'
            elif kind == 'leaf':
                assert False, 'leaf must be the deepest node'
        # The deepest node is a leaf whose value_ref must be len||sha256(initial)
        kind, *fields = parse_node(chain[-1], None)
        assert kind == 'leaf', f'deepest node is {kind}, not leaf, for {name!r}'
        hp, value_ref, _mem = fields
        assert value_ref[:4] == u32le(72), f'leaf value length for {name!r}'
        assert value_ref[4:] == hashlib.sha256(accounts[name]).digest(), \
            f'leaf value hash does not match table initial bytes for {name!r}'
    return {'accounts': len(accounts), 'root': pre_state_root.hex()}


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('paths_json')
    p.add_argument('ledger_fixture')
    p.add_argument('report')
    a = p.parse_args()
    result = check(a.paths_json, a.ledger_fixture)

    # Negative checks: mutated root/node/value must reject.
    import copy
    raw = json.loads(Path(a.paths_json).read_text())
    negatives = 0
    # 1. flipped pre_state_root bit
    m = copy.deepcopy(raw); m['pre_state_root'][0] ^= 1
    Path('/tmp/opencode/mut-paths-root.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-paths-root.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated root accepted')
    # 2. flipped byte in the first node serialization of account 0
    m = copy.deepcopy(raw); m['accounts'][0]['node_serializations'][0][0] ^= 1
    Path('/tmp/opencode/mut-paths-node.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-paths-node.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated node accepted')
    # 3. flipped byte in the deepest (leaf) node of account 0
    m = copy.deepcopy(raw); m['accounts'][0]['node_serializations'][-1][10] ^= 1
    Path('/tmp/opencode/mut-paths-leaf.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-paths-leaf.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated leaf accepted')
    # 4. swapped leaf value with another account's (name/table mismatch)
    names = [bytes(x['receiver']) for x in raw['accounts']]
    if len(names) >= 2:
        m = copy.deepcopy(raw)
        m['accounts'][0]['receiver'], m['accounts'][1]['receiver'] = m['accounts'][1]['receiver'], m['accounts'][0]['receiver']
        Path('/tmp/opencode/mut-paths-swap.json').write_text(json.dumps(m))
        try:
            check('/tmp/opencode/mut-paths-swap.json', a.ledger_fixture)
        except AssertionError:
            negatives += 1
        else:
            raise AssertionError('swapped witness accepted')
    result['negative_checks'] = negatives
    result['status'] = 'HOST_AUDITED_PRE_STATE_PATHS_NOT_CIRCUIT_PROOF'
    Path(a.report).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
