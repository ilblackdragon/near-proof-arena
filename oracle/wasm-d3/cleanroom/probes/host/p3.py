from hp import *
import re
C = []
PK = b"\x00" + bytes(range(32))
SK = b"\x01" + bytes(range(64))
for acct in [b"bob.near", b"alice.near", b"bobbobbobbob.near"]:
  for pk in [PK, SK]:
    L = len(acct)
    base = acct + pk + (7).to_bytes(16, "little") + b"m1,m2"
    o = L + len(pk)
    for nn in [0, 1, 2]:
        C.append((f"gfa {acct.decode()} {len(pk)} {nn}", P(base).call("promise_batch_create", L, 0).call("promise_batch_action_add_gas_key_with_full_access", 0, len(pk), L, nn).done(False)))
        C.append((f"gfc {acct.decode()} {len(pk)} {nn}", P(base).call("promise_batch_create", L, 0).call("promise_batch_action_add_gas_key_with_function_call", 0, len(pk), L, nn, o, 8, 0, 5, o+16).done(False)))
    C.append((f"tgk {acct.decode()} {len(pk)}", P(base).call("promise_batch_create", L, 0).call("promise_batch_action_transfer_to_gas_key", 0, len(pk), L, o).done(False)))
a = near([c for _, c in C]); b = mine([c for _, c in C])
for (l, _), x, y in zip(C, a, b):
    xb, xu = map(int, x.split()[1:3]); yb, yu = map(int, y.split()[1:3])
    print(f"{l:34s} dburn {xb-yb:14d} duse-dburn {(xu-yu)-(xb-yb):16d}  {x.split('||')[0][:60]}")
