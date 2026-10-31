#!/usr/bin/env python3
"""Synthesize a scaled NPMULF01 fixture: replicate the original 804-receipt
list body k times with DISTINCT receipt ids and fresh outcome digests, so the
distinct-ID and per-list constraints hold. Deposit fields preserved from the
original (the ledger is re-derived from the account table, so balance
consistency is maintained by construction in the audit model: initial/final
from the ORIGINAL table still bind because we only need the fixture to
EXERCISE the circuit geometry, not to match a real trie).

This is a GEOMETRY/SCALING fixture, not a claim-derived one: the packet it
proves binds the fixture's own digests, and the audit checks are run against
the same fixture. No native claim is claimed for it.
"""
import struct
import sys
from pathlib import Path


def le_words(blob, off, n):
    return list(struct.unpack_from(f'<{n}Q', blob, off))


def main():
    src_multi = Path(sys.argv[1]).read_bytes()      # original NPMULF01
    reps = int(sys.argv[2])                          # body repetitions
    out_path = Path(sys.argv[3])
    assert src_multi[:8] == b'NPMULF01'
    n_lists = struct.unpack_from('<I', src_multi, 8)[0]
    pos = 12
    parts = []
    for _ in range(n_lists):
        sz = struct.unpack_from('<Q', src_multi, pos)[0]; pos += 8
        parts.append(bytearray(src_multi[pos:pos+sz])); pos += sz
    # Scale ONLY the big list (index 2); small lists stay original.
    big = parts[2]
    n0 = struct.unpack_from('<I', big, 40)[0]
    body0 = bytes(big[76:76+504*n0])
    new_n = n0 * reps
    # Receipt ids live in words 30..33 of each receipt (offset 76 + i*504 + 30*8).
    out = bytearray()
    for i in range(new_n):
        rec = bytearray(body0[(i % n0)*504:(i % n0)*504+504])
        # distinct id: word30 = i, word31 = 0xA5A5A5A5 (marks synthetic)
        struct.pack_into('<Q', rec, 30*8, i)
        struct.pack_into('<Q', rec, 31*8, 0x5A5A5A5A00000000 + reps)
        # fresh outcome digest words 59..62 (deterministic from i)
        h = (i * 0x9E3779B97F4A7C15 + 0x1234_5678) & (2**64-1)
        struct.pack_into('<Q', rec, 59*8, h)
        out += rec
    new_big = bytearray()
    new_big += big[:76]
    struct.pack_into('<I', new_big, 40, new_n)
    new_big += out
    assert len(new_big) == 76 + 504*new_n
    parts[2] = new_big
    enc = bytearray(b'NPMULF01' + struct.pack('<I', n_lists))
    for p in parts:
        enc += struct.pack('<Q', len(p)) + p
    out_path.write_bytes(bytes(enc))
    total = struct.unpack_from('<I', parts[0], 40)[0] + struct.unpack_from('<I', parts[1], 40)[0] + new_n
    print(f'{out_path}: lists={n_lists} big={new_n} total_receipts={total} bytes={len(enc)}')


if __name__ == '__main__':
    main()
