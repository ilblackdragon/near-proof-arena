#!/usr/bin/env python3
"""Host-verify synthetic variable-depth trie fixtures (NPMTRIE02).

Rehashes every exported chain against the fixture root and checks key-path
correspondence (key = nibbles(0x00||name)), value_ref binding, and fragment
equality — the same reference logic as audit_account_paths.py, applied to
the synthetic NPMTRIE02 format (per-account full chains, no shared prefix).
"""
import hashlib
import json
import struct
import sys
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
        return ('leaf', ser[5:5+hplen], ser[5+hplen:5+hplen+36], ser[ser.len()-8:] if False else ser[5+hplen+36:5+hplen+44])
    if tag == 3:
        hplen = struct.unpack_from('<I', ser, 1)[0]
        return ('ext', ser[5:5+hplen], ser[5+hplen:5+hplen+32])
    if tag in (1, 2):
        pos = 1
        if tag == 2:
            pos = 37
        bitmap = struct.unpack_from('<H', ser, pos)[0]
        pos += 2
        kids = [n for n in range(16) if bitmap >> n & 1]
        children = []
        for _ in kids:
            children.append(ser[pos:pos+32])
            pos += 32
        return ('branch', kids, children)
    raise ValueError(f'tag {tag}')


def check(fixture_path):
    raw = Path(fixture_path).read_bytes()
    assert raw[:9] == b'NPMTRIE02'
    root = raw[9:41]
    # u16 chain_len(unused, 0) at 41; u16 shared_count(0) at 43; count at 45.
    pos = 45
    count = struct.unpack_from('<H', raw, pos)[0]
    pos += 2
    checked = 0
    for _ in range(count):
        chain_len = struct.unpack_from('<H', raw, pos)[0]
        pos += 2
        chain = []
        for _ in range(chain_len):
            nlen = struct.unpack_from('<H', raw, pos)[0]
            pos += 2
            chain.append(raw[pos:pos+nlen])
            pos += nlen
        name_len = struct.unpack_from('<Q', raw, pos)[0]
        pos += 8
        name = raw[pos:pos+name_len]
        pos += 64
        initial = raw[pos:pos+72]
        pos += 72
        # Verify: top hashes to root; links follow the key; leaf binds value.
        key = nib(bytes([0]) + name)
        assert hashlib.sha256(chain[0]).digest() == root, f'{name}: root'
        kpos = 0
        for parent, child in zip(chain, chain[1:]):
            kind = parent[0]
            child_hash = hashlib.sha256(child).digest()
            if kind == 1:
                kids, children = parse_node(parent)[1], parse_node(parent)[2]
                c = key[kpos]
                assert c in kids, f'{name}: nibble {c} missing'
                assert children[kids.index(c)] == child_hash, f'{name}: link'
                kpos += 1
            elif kind == 3:
                frag = hp_decode(parse_node(parent)[1])
                assert frag == key[kpos:kpos+len(frag)], f'{name}: ext frag'
                assert parse_node(parent)[2] == child_hash, f'{name}: ext link'
                kpos += len(frag)
            else:
                raise AssertionError(f'{name}: leaf mid-chain')
        # Leaf.
        leaf = chain[-1]
        assert leaf[0] == 0, f'{name}: not leaf'
        hplen = struct.unpack_from('<I', leaf, 1)[0]
        frag = hp_decode(leaf[5:5+hplen])
        assert frag == key[kpos:kpos+len(frag)], f'{name}: leaf frag'
        kpos += len(frag)
        assert kpos == len(key), f'{name}: path end'
        vref = leaf[5+hplen:5+hplen+36]
        assert vref[:4] == struct.pack('<I', 72), f'{name}: vref len'
        assert vref[4:] == hashlib.sha256(initial).digest(), f'{name}: vref hash'
        checked += 1
    assert pos == len(raw), 'trailing bytes'
    return checked, root.hex()


if __name__ == '__main__':
    total = 0
    for f in sorted(Path(sys.argv[1]).glob('*.bin')):
        n, root = check(f)
        total += n
        print(f'{f.stem}: {n} chains OK, root {root[:16]}')
    print(f'total chains verified: {total}')
