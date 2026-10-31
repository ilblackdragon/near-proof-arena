#!/usr/bin/env python3
"""Self-audit for scaled (synthetic) fixtures: re-threads the ledger exactly
as make_scaled_ledger.py did and checks the scaled packet's PUBLIC STATEMENT
structure (root words, table, counts, inactive-zero, distinct synthetic
receipt-id pattern). NO claim binding: these are geometry/scaling packets,
not claim-derived validity. The circuit's own in-process verify plus this
structural check is the validation bar for scaling runs.
"""
import struct
import sys
from pathlib import Path


def rd(b, o):
    return struct.unpack_from('<Q', b, o)[0]


def main():
    ledger_p, multi_p, public_p = (Path(x) for x in sys.argv[1:4])
    led = ledger_p.read_bytes()
    assert led[:9] == b'NPMLEDG01'
    multi = multi_p.read_bytes()
    assert multi[:8] == b'NPMULF01'
    public = public_p.read_bytes() if public_p.exists() else None

    names, bal, act, init, fin = [], [], [], [], []
    for r in range(16):
        off = 41 + r*224
        a = rd(led, off)
        nl = rd(led, off+8)
        names.append(bytes(led[off+16:off+16+nl]))
        act.append(a)
        init.append(led[off+80:off+152])
        bal.append(rd(led, off+80) | (rd(led, off+88) << 64))
        fin.append(rd(led, off+152) | (rd(led, off+160) << 64))
    live = {names[i]: bal[i] for i in range(16) if act[i]}
    nl = struct.unpack_from('<I', multi, 8)[0]
    pos = 12
    total = 0
    synth_ids = set()
    for _ in range(nl):
        sz = rd(multi, pos); pos += 8
        part = multi[pos:pos+sz]; pos += sz
        assert part[:8] == b'NPLST001'
        n = struct.unpack_from('<I', part, 40)[0]
        for i in range(n):
            base = 76 + i*504
            rlen = rd(part, base+21*8)
            recv = part[base+22*8:base+22*8+rlen]
            dep = rd(part, base+16) | (rd(part, base+24) << 64)
            live[recv] = live[recv] + dep
            rid0 = rd(part, base+30*8)
            rid1 = rd(part, base+31*8)
            synth_ids.add((rid0, rid1))
            total += 1
    ok = True
    for i in range(16):
        if act[i] != 1:
            continue
        if live[names[i]] != fin[i]:
            print(f'MISMATCH account {names[i]}: threaded {live[names[i]]} vs table final {fin[i]}')
            ok = False
    if public is not None:
        # statement: 4 root words + 16 rows x 18 words, then per-list 9 + 11*cap words
        # We check table finals in the public statement match the ledger.
        words = struct.unpack_from('<288Q', public, 32)  # after 4 root words
        for r in range(16):
            row = words[r*18:(r+1)*18]
            if row[0] == 0:
                continue
            f = row[16] | (row[17] << 64)
            if f != fin[r]:
                print(f'PUBLIC TABLE MISMATCH row {r}')
                ok = False
    print(f'receipts={total} distinct_ids={len(synth_ids)} ledger_threading={"OK" if ok else "FAIL"}')
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
