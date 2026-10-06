from hp import *
C = []
for pk in [b"\x00"+bytes(31), b"\x07"+bytes(32), b"\x00"+bytes(33), b"", b"\x01"+bytes(64), b"\x02"+bytes(1952), b"\x01"+bytes(63), b"\x00"+bytes(range(32))]:
    base = b"bob.near" + (7).to_bytes(16, "little") + pk
    C.append((f"tgk {pk[:1].hex()} {len(pk)}", P(base).call("promise_batch_create", 8, 0).call("promise_batch_action_transfer_to_gas_key", 0, len(pk), 24, 8).done(False)))
    C.append((f"stake {pk[:1].hex()} {len(pk)}", P(base).call("promise_batch_create", 8, 0).call("promise_batch_action_stake", 0, 8, len(pk), 24).done(False)))
    C.append((f"afk {pk[:1].hex()} {len(pk)}", P(base).call("promise_batch_create", 8, 0).call("promise_batch_action_add_key_with_full_access", 0, len(pk), 24, 3).done(False)))
    C.append((f"dk {pk[:1].hex()} {len(pk)}", P(base).call("promise_batch_create", 8, 0).call("promise_batch_action_delete_key", 0, len(pk), 24).done(False)))
    C.append((f"gfa {pk[:1].hex()} {len(pk)}", P(base).call("promise_batch_create", 8, 0).call("promise_batch_action_add_gas_key_with_full_access", 0, len(pk), 24, 3).done(False)))
cmp(C, 250)
