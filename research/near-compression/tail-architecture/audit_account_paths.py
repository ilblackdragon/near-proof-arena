#!/usr/bin/env python3
"""Host audit for in-circuit trie membership (reference model, NPMTRIE01).

Verifies, from the trie-path JSON + ledger fixture:
- chain correspondence: root node hashes to the claim prev_state_root; each
  deeper node's hash is embedded in its parent at the position selected by
  the account's KEY NIBBLES (branch: rank among set bitmap bits; ext: after
  the fragment) — the key-path correspondence the old audit lacked;
- key derivation: key = nibbles(0x00 || name); branch steps consume exactly
  one nibble; ext/leaf hexPrefix fragments equal the key nibbles at the
  current position; the path ends exactly at the leaf;
- leaf value binding: value_ref == u32le(72) || sha256(initial bytes).

This is the INDEPENDENT reference for what the circuit now proves; the
circuit is the binding, this checks the same relation host-side.
"""
import argparse
import copy
import hashlib
import json
import struct
from pathlib import Path


def nib(b):
    out = []
    for x in b:
        out += [x >> 4, x & 15]
    return out


def hp_decode(b):
    if not b:
        return []
    f = b[0]
    return ([f & 15] if (f >> 4) & 1 else []) + nib(b[1:])


def parse_node(ser):
    tag = ser[0]
    if tag == 0:
        hplen = struct.unpack_from('<I', ser, 1)[0]
        hp = ser[5:5+hplen]
        value_ref = ser[5+hplen:5+hplen+36]
        mem = struct.unpack_from('<Q', ser, 5+hplen+36)[0]
        assert 5+hplen+36+8 == len(ser)
        return ('leaf', hp, value_ref, mem)
    if tag == 3:
        hplen = struct.unpack_from('<I', ser, 1)[0]
        hp = ser[5:5+hplen]
        child = ser[5+hplen:5+hplen+32]
        mem = struct.unpack_from('<Q', ser, 5+hplen+32)[0]
        assert 5+hplen+32+8 == len(ser)
        return ('ext', hp, child, mem)
    if tag in (1, 2):
        pos = 1
        value_ref = None
        if tag == 2:
            value_ref = ser[1:37]
            pos = 37
        bitmap = struct.unpack_from('<H', ser, pos)[0]
        pos += 2
        kids = [n for n in range(16) if bitmap >> n & 1]
        children = []
        for _ in kids:
            children.append(ser[pos:pos+32])
            pos += 32
        mem = struct.unpack_from('<Q', ser, pos)[0]
        pos += 8
        assert pos == len(ser)
        return ('branch', value_ref, children, mem, kids)
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
            initial = row[80:152]
            accounts[name] = initial
        off += 224
    # New-format JSON: shared chain + per-account leaf.
    shared = [bytes(x) for x in paths.get('shared', [])]
    entries = []
    if shared:
        assert len(shared) == paths['chain_len']-1, 'shared chain length'
        for a in paths['accounts']:
            name = bytes(a['receiver'])
            assert name in accounts, f'witness for unknown account {name!r}'
            entries.append((name, shared + [bytes(a['leaf'])]))
    else:
        # Legacy per-account chains (full chain per account).
        for a in paths['accounts']:
            name = bytes(a['receiver'])
            assert name in accounts
            entries.append((name, [bytes(x) for x in a['node_serializations']]))
    for name, chain in entries:
        key = nib(bytes([0]) + name)
        # Root.
        node_hash = hashlib.sha256(chain[0]).digest()
        assert node_hash == pre_state_root, f'root chain mismatch for {name!r}'
        pos = 0
        for parent, child in zip(chain, chain[1:]):
            kind, *fields = parse_node(parent)
            child_hash = hashlib.sha256(child).digest()
            if kind == 'branch':
                value_ref, children, _mem, kids = fields
                c = key[pos]
                assert c in kids, f'{name!r}: key nibble {c} missing at pos {pos}'
                assert children[kids.index(c)] == child_hash, f'{name!r}: branch link mismatch at pos {pos}'
                pos += 1
            elif kind == 'ext':
                hp, embedded, _mem = fields
                frag = hp_decode(hp)
                assert frag == key[pos:pos+len(frag)], f'{name!r}: ext fragment mismatch'
                assert embedded == child_hash, f'{name!r}: ext link mismatch'
                pos += len(frag)
            else:
                raise AssertionError(f'{name!r}: leaf before path end')
        # Leaf.
        kind, *fields = parse_node(chain[-1])
        assert kind == 'leaf', f'{name!r}: deepest node is {kind}, not leaf'
        hp, value_ref, _mem = fields
        frag = hp_decode(hp)
        assert frag == key[pos:pos+len(frag)], f'{name!r}: leaf fragment mismatch'
        pos += len(frag)
        assert pos == len(key), f'{name!r}: path length {pos} != key length {len(key)}'
        assert value_ref[:4] == struct.pack('<I', 72), f'{name!r}: leaf value length'
        assert value_ref[4:] == hashlib.sha256(accounts[name]).digest(), \
            f'{name!r}: leaf value hash does not match table initial bytes'
    return {'accounts': len(entries), 'root': pre_state_root.hex()}


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('paths_json')
    p.add_argument('ledger_fixture')
    p.add_argument('report')
    a = p.parse_args()
    result = check(a.paths_json, a.ledger_fixture)
    raw = json.loads(Path(a.paths_json).read_text())
    negatives = 0
    # 1. Root lie.
    m = copy.deepcopy(raw); m['pre_state_root'][0] ^= 1
    Path('/tmp/opencode/mut-t-root.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-t-root.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated root accepted')
    # 2. Node lie (first shared node byte).
    m = copy.deepcopy(raw); m['shared'][0][0] ^= 1
    Path('/tmp/opencode/mut-t-node.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-t-node.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated node accepted')
    # 3. Leaf value lie.
    m = copy.deepcopy(raw); m['accounts'][0]['leaf'][10] ^= 1
    Path('/tmp/opencode/mut-t-leaf.json').write_text(json.dumps(m))
    try:
        check('/tmp/opencode/mut-t-leaf.json', a.ledger_fixture)
    except AssertionError:
        negatives += 1
    else:
        raise AssertionError('mutated leaf accepted')
    # 4. Witness swap between accounts (path correspondence must reject).
    if len(raw['accounts']) >= 2:
        m = copy.deepcopy(raw)
        m['accounts'][0]['leaf'], m['accounts'][1]['leaf'] = m['accounts'][1]['leaf'], m['accounts'][0]['leaf']
        Path('/tmp/opencode/mut-t-swap.json').write_text(json.dumps(m))
        try:
            check('/tmp/opencode/mut-t-swap.json', a.ledger_fixture)
        except AssertionError:
            negatives += 1
        else:
            raise AssertionError('swapped witness accepted')
    result['negative_checks'] = negatives
    result['status'] = 'REFERENCE_MODEL_FOR_IN_CIRCUIT_TRIE_MEMBERSHIP'
    Path(a.report).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
