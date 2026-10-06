from probe import *
G = 300 * 10**12
c = []
def add(l, h, gas=G): c.append((l, f"{gas} {h}"))
def pm(steps, blob=b"bob.near" + b"f" + (10**20).to_bytes(16, "little") + (1).to_bytes(16, "little") + (10**24).to_bytes(16, "little")):
    """steps: list of ('create', len, ptr) | ('fc', idx, mlen, mptr, alen, aptr, amt_ptr, gas)"""
    m = Module()
    m.vr = m.import_func("env", "value_return", [I64, I64], [])
    pc = m.import_func("env", "promise_batch_create", [I64, I64], [I64])
    fc = m.import_func("env", "promise_batch_action_function_call", [I64] * 7, [])
    m.memory = (1, None)
    m.datas.append(b"\x00" + i32c(0) + b"\x0b" + vec([bytes([x]) for x in blob]))
    body = bytearray()
    for s in steps:
        if s[0] == "create":
            body += i64c(s[1]) + i64c(s[2]) + b"\x10" + uleb(pc) + b"\x1a"
        else:
            for a in s[1:]:
                body += i64c(a)
            body += b"\x10" + uleb(fc)
    m.func([], [], [], bytes(body))
    m.exports.append(("main", 0, len(m.imports)))
    return m.encode().hex()
CR = ("create", 8, 0)
M, A0, A1, ABAL = 8, 9, 25, 41      # method ptr, amount ptrs (1e20, 1, 1e24)
OOB = 2**26
add("ok", pm([CR, ("fc", 0, 1, M, 0, 0, A0, 10**12)]))
add("bad idx + empty method", pm([CR, ("fc", 5, 0, M, 0, 0, A0, 10**12)]))
add("bad idx + method OOB", pm([CR, ("fc", 5, 1, OOB, 0, 0, A0, 10**12)]))
add("bad idx + args OOB", pm([CR, ("fc", 5, 1, M, 4, OOB, A0, 10**12)]))
add("bad idx + amount OOB", pm([CR, ("fc", 5, 1, M, 0, 0, OOB, 10**12)]))
add("empty method + amount OOB", pm([CR, ("fc", 0, 0, M, 0, 0, OOB, 10**12)]))
add("empty method + args OOB", pm([CR, ("fc", 0, 0, M, 4, OOB, A0, 10**12)]))
add("bad idx + prepay too much", pm([CR, ("fc", 5, 1, M, 0, 0, A0, 10**15)]))
add("balance + prepay too much", pm([CR, ("fc", 0, 1, M, 0, 0, ABAL + 0, 10**15)]))
add("method register path", pm([CR, ("fc", 0, -1, 3, 0, 0, A0, 10**12)]))
add("args register path", pm([CR, ("fc", 0, 1, M, -1, 3, A0, 10**12)]))
add("amount 1e24 then 1 (one-yocto)", pm([CR, ("fc", 0, 1, M, 0, 0, ABAL, 0), ("fc", 0, 1, M, 0, 0, A1, 0)]))
add("amount 1e24 then 1e20", pm([CR, ("fc", 0, 1, M, 0, 0, ABAL, 0), ("fc", 0, 1, M, 0, 0, A0, 0)]))
add("amount 1 twice", pm([CR, ("fc", 0, 1, M, 0, 0, A1, 0), ("fc", 0, 1, M, 0, 0, A1, 0)]))
add("create register path", pm([("create", -1, 0)]))
add("create OOB", pm([("create", 8, OOB)]))
add("create len 0", pm([("create", 0, 0)]))
add("two fcs on one promise, sir", pm([("create", 10, 57), ("fc", 0, 1, M, 3, 0, A0, 10**12), ("fc", 0, 1, M, 3, 0, A1, 10**12)], blob=b"bob.near" + b"f" + (10**20).to_bytes(16, "little") + (1).to_bytes(16, "little") + (10**24).to_bytes(16, "little") + b"alice.near"))
add("prepay exceeds after promises", pm([CR, ("fc", 0, 1, M, 0, 0, A0, 2 * 10**14), ("fc", 0, 1, M, 0, 0, A0, 10**14)]))
add("prepay exceeds (low gas)", pm([CR, ("fc", 0, 1, M, 0, 0, A0, 10**12)]), 10**12)
add("gas u64 max", pm([CR, ("fc", 0, 1, M, 0, 0, A0, -1)]))
for g in [3 * 10**11, 3.1e11, 3.2e11, 3.3e11]:
    add(f"function_call fees low gas {g}", pm([CR, ("fc", 0, 1, M, 0, 0, A0, 0)]), int(g))
cmp(c)
