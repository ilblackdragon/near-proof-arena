#!/usr/bin/env python3
"""Re-derive the NPMLEDG01 ledger for a scaled fixture: thread the ORIGINAL
table's initial balances through the scaled receipt stream in application
order (registers update before += deposit), then write the computed finals
back into the table. The trie fixture stays the ORIGINAL one (initial values
unchanged -> trie membership still verifies); only the final-balance column
changes. This keeps every circuit constraint satisfiable:
 - before==register: by construction of the threading
 - register += deposit: same
 - final==register: written from the threading
 - trie leaf value_ref binds INITIAL bytes: unchanged
Receipt ids/digests don't enter the ledger; account names match the original.
"""
import struct
import sys
from pathlib import Path


def rd(blob, off):
    return struct.unpack_from('<Q', blob, off)[0]


def main():
    ledger_p = Path(sys.argv[1])
    multi_p = Path(sys.argv[2])
    out_p = Path(sys.argv[3])
    led = bytearray(ledger_p.read_bytes())
    assert led[:9] == b'NPMLEDG01'
    # load initial balances + names
    names, bal, act = [], [], []
    for r in range(16):
        off = 41 + r*224
        a = rd(led, off)
        nl = rd(led, off+8)
        names.append(bytes(led[off+16:off+16+nl]))
        bal.append(rd(led, off+80) | (rd(led, off+88) << 64))
        act.append(a)
    # thread the scaled receipts
    raw = multi_p.read_bytes()
    assert raw[:8] == b'NPMULF01'
    nl = struct.unpack_from('<I', raw, 8)[0]
    pos = 12
    bal = {names[i]: bal[i] for i in range(16) if act[i]}
    for _ in range(nl):
        sz = rd(raw, pos); pos += 8
        part = raw[pos:pos+sz]; pos += sz
        assert part[:8] == b'NPLST001'
        n = struct.unpack_from('<I', part, 40)[0]
        for i in range(n):
            base = 76 + i*504
            rlen = rd(part, base+21*8)
            recv = part[base+22*8:base+22*8+rlen]
            dep = rd(part, base+16) | (rd(part, base+24) << 64)
            bal[recv] = bal[recv] + dep
    # write finals
    for r in range(16):
        off = 41 + r*224
        if act[r] != 1:
            continue
        v = bal[names[r]]
        struct.pack_into('<QQ', led, off+152, v & (2**64-1), v >> 64)
    out_p.write_bytes(bytes(led))
    print(f'{out_p}: 16 rows, finals recomputed for {len(bal)} accounts')


if __name__ == '__main__':
    main()
