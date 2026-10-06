from hp import *
C = []
PK = b"\x00" + bytes(range(32))
for names in [b"a,,b", b"\xff,,b", b"\xff,b", b",", b"", b"a,", b"\xc3,\xa9", b"a\x00b", b"x"*3000]:
    for pk in [PK, PK[:-1]]:
        D = b"bob.near" + pk + (7).to_bytes(16, "little") + names
        o = 8 + len(pk)
        C.append((f"afc {names[:8]!r} {len(pk)}", P(D).call("promise_batch_create", 8, 0).call("promise_batch_action_add_key_with_function_call", 0, len(pk), 8, 0, o, 8, 0, len(names), o + 16).done(False)))
        C.append((f"afc bad idx {names[:8]!r} {len(pk)}", P(D).call("promise_batch_create", 8, 0).call("promise_batch_action_add_key_with_function_call", 5, len(pk), 8, 0, o, 8, 0, len(names), o + 16).done(False)))
cmp(C, 300)
