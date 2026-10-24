#!/usr/bin/env python3
"""Host checks for ordered source sets and their outcome root; proof verification separate."""
import hashlib
import struct
from audit_source_membership import root_from_digest
from audit_public_merkle import reconstruct


def require(ok, message):
    if not ok:
        raise ValueError(message)


def encode(packet, paths):
    return (b'NPMSET01' + struct.pack('<I', len(packet)) + packet + struct.pack('<I', len(paths)) +
            b''.join(struct.pack('<I', len(p)) + b''.join(bytes([x['direction']]) + bytes(x['sibling']) for x in p) for p in paths))


def check(envelope, caps, mode, expected, outcome_root):
    """Return packet/public after claim-relative checks, NOT proof acceptance.

    expected comes from trusted claim-only derivation; outcome_root from expected
    claim. Caller must verify returned packet with returned public and fixed caps/
    mode. Account state, routing and runtime validity are not established here.
    """
    require(16 <= len(envelope) <= 300000 and envelope[:8] == b'NPMSET01', 'envelope')
    size = struct.unpack_from('<I', envelope, 8)[0]
    pos = 12 + size
    require(size >= 24 and pos+4 <= len(envelope), 'packet framing')
    packet = envelope[12:pos]
    count = struct.unpack_from('<I', envelope, pos)[0]
    pos += 4
    require(count == len(caps) == len(expected['sources']), 'complete source count')
    paths = []
    for _ in range(count):
        require(pos+4 <= len(envelope), 'path header')
        depth = struct.unpack_from('<I', envelope, pos)[0]
        pos += 4
        require(pos+33*depth <= len(envelope), 'path length')
        paths.append([{'direction': envelope[pos+33*i], 'sibling': list(envelope[pos+33*i+1:pos+33*i+33])} for i in range(depth)])
        pos += 33*depth
    require(pos == len(envelope), 'trailing data')
    header = 16+4*count
    require(len(packet) >= header+8 and packet[:8] == b'NPMULT01', 'packet version')
    require(struct.unpack_from('<I', packet, 8)[0] == count, 'profile count')
    require(list(struct.unpack_from('<'+str(count)+'I', packet, 12)) == caps, 'profile capacities')
    require(struct.unpack_from('<I', packet, 12+4*count)[0] == mode, 'profile mode')
    plen = struct.unpack_from('<Q', packet, header)[0]
    require(plen == 8*sum(9+11*c for c in caps) and header+8+plen <= len(packet), 'public framing')
    public = packet[header+8:header+8+plen]
    off = 0
    leaves, ids, counts = [], [], []
    for index, cap in enumerate(caps):
        words = struct.unpack_from('<'+str(9+11*cap)+'Q', public, off)
        require(list(words[:4]) == expected['context'], 'claim context')
        n = words[4]
        require(n <= cap, 'receipt count')
        counts.append(n)
        leaf = b''.join(x.to_bytes(8, 'big') for x in words[5:9])
        require(root_from_digest(leaf, paths[index]) == bytes(expected['sources'][index]['root']), 'ordered source membership')
        for i in range(cap):
            row = words[9+11*i:20+11*i]
            if i >= n:
                require(not any(row), 'inactive output')
                continue
            require(row[0] == 1 and row[1] == i, 'ordered active output')
            rid = struct.pack('<4Q', *row[3:7])
            ids.append(rid)
            h = b''.join(x.to_bytes(8, 'big') for x in row[7:11])
            leaves.append(hashlib.sha256(struct.pack('<I', 2)+rid+h).digest())
        off += 8*(9+11*cap)
    require(len(set(ids)) == len(ids), 'duplicate receipt id')
    root = reconstruct(leaves)[1] or bytes(32)
    require(root == outcome_root, 'claim outcome root')
    return packet, public, counts
