#!/usr/bin/env python3
"""B-T2 (M6.4): lane A's HOST messages for T1's `storage_write`, as a `tracegen.py --host-join` file.

  join_laneA.py STATE.json SEGCHECK_LOG OUT.json

Lane A's joined segment AIR (`wasmBaseSegAirMPJ`, a-t1/README §5) leaves exactly 8 messages
unbalanced on T1's call segment: `storage_write`'s HOSTQ (208), HOSTR (209) and 6 HOSTB (210)
request bytes. The log prints the first three verbatim (HOSTQ, HOSTR, the key byte); the other five
are the value buffer's bytes at `value_ptr + j` under wire id `58 + 256 = 314` — the call's value,
i.e. T1's committed value of the key (checked here: 5 bytes, the log's `value_len`). The STATE
rows of `m5tSegH` must answer exactly these messages.
"""
import ast
import json
import re
import sys

st = json.load(open(sys.argv[1]))
log = open(sys.argv[2]).read()
m = re.search(r'first (\[.*\])\s*$', log, re.M)
first = ast.literal_eval(m.group(1).replace('Some(', '(').replace('None', 'None'))
by = {}
for (bus, msg), cnt, _src in first:
    by.setdefault(bus, []).append((msg, cnt))
(q, cq), = by[208]
(r, cr), = by[209]
(kb, ck), = by[210]
assert cq == 1 and cr == -1 and ck == 1, 'lane A sends HOSTQ / HOSTB and receives HOSTR'
ts, hid, S, np_ = q[:4]
args = [q[4 + 2 * j] + (q[5 + 2 * j] << 32) for j in range(9)]
klen, kptr, vlen, vptr, rid = args[:5]
assert hid == 58 and np_ == 5 and klen == 1 and kb[:4] == [ts, 58, 0, kptr]
key_byte = kb[4]
# the contract's data key for that one-byte key: 0x09 ‖ account ‖ ',' ‖ key
cands = [k for k, v in st['changes'] if k.startswith('09') and k.endswith('2c%02x' % key_byte)]
assert len(cands) == 1, cands
key = cands[0]
v = bytes.fromhex(dict(st['changes'])[key])
assert len(v) == vlen
msgs = [[208, True, q], [209, False, r], [210, True, kb]]
msgs += [[210, True, [ts, 58 + 256, 0, vptr + j, b]] for j, b in enumerate(v)]
J = {key: dict(ts=ts, S=S, rid=rid, kptr=kptr, vptr=vptr, rlo=r[2], rhi=r[3], glo=r[4], ghi=r[5],
               msgs=msgs, source='lane A a-t1/logs/j-t1-segcheck.txt (HOSTQ, HOSTR, key byte verbatim); '
               'value bytes = T1 committed value of the key at value_ptr + j, wire 314')}
json.dump(J, open(sys.argv[3], 'w'), indent=1)
print(json.dumps(dict(key=key, ts=ts, S=S, rid=rid, kptr=kptr, vptr=vptr, vlen=vlen, evicted=r[2],
                      g_after=r[4] + (r[5] << 32))))
