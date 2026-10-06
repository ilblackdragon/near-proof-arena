from hp import *
C = []
A = b"bob.near" + (0).to_bytes(8, "little")
def many(n, then):
    p = P(A, gas=10**15)
    p.raw(b"\x02\x40\x03\x40" + i64c(8) + i64c(0) + b"\x10" + uleb(0))  # placeholder replaced below
    return p
# build loop manually: call promise_batch_create n times via unrolled code
for n, tail in [(1024, None), (1025, None), (1024, "and"), (1024, "then"), (1024, "yield")]:
    p = P(A + b"m", gas=10**15)
    for _ in range(n):
        p.call("promise_batch_create", 8, 0, store=False)
    if tail == "and": p.call("promise_and", 8, 1, store=False)
    if tail == "then": p.call("promise_batch_then", 0, 8, 0, store=False)
    if tail == "yield": p.call("promise_yield_create", 1, 16, 0, 0, 10**9, 0, 0, store=False)
    C.append((f"promises {n} {tail}", p.done(False)))
# write_register size and register_len after limits; read_register missing
C.append(("readreg missing", P().call("read_register", 7, 0).done()))
C.append(("readreg oob", P(b"ab").call("write_register", 1, 2, 0).call("read_register", 1, 2**40).done()))
C.append(("storage key reg", P(b"k"*3000).call("write_register", 1, 2049, 0).call("storage_has_key", U64MAX, 1).done()))
C.append(("storage read key reg 2048", P(b"k"*3000).call("write_register", 1, 2048, 0).call("storage_read", U64MAX, 1, 1).done()))
C.append(("storage remove missing", P(b"k").call("storage_remove", 1, 0, 1).call("register_len", 1).done()))
C.append(("storage write reg value", P(b"kv").call("write_register", 3, 1, 1).call("storage_write", 1, 0, U64MAX, 3, 3).call("storage_read", 1, 0, 4).call("read_register", 4, 100).done((100, 8))))
C.append(("storage write same key reg", P(b"kv").call("storage_write", 1, 0, 1, 1, 0).call("storage_write", 1, 0, 1, 0, 0).call("register_len", 0).call("storage_usage").done()))
C.append(("vr receivers reg", P(b"abc", opts="rcv=alice.near,bob.near").call("write_register", 0, 3, 0).call("value_return", U64MAX, 0).done(False)))
C.append(("input empty", P().call("input", 0).call("register_len", 0).done()))
C.append(("promise_result S empty", P(opts="results=S").call("promise_result", 0, 2).call("register_len", 2).done()))
C.append(("used_gas after promise", P(b"bob.near" + bytes(16) + b"m").call("promise_create", 8, 0, 1, 24, 0, 0, 8, 10**13).call("used_gas").call("prepaid_gas").done()))
cmp(C, 250)
C = []
YD = b"bob.near" + (0).to_bytes(8, "little") + b"m" + bytes(range(32)) + bytes(16)
for amt in [57, 0]:
    p = P(YD, gas=10**15)
    for _ in range(1024):
        p.call("promise_batch_create", 8, 0, store=False)
    p.call("promise_yield_create_with_id", 1, 16, 0, 0, 49 if amt == 0 else 1000, 10**9, 0, 32, 17, store=False)
    C.append((f"1024 yield_with_id amt{amt}", p.done(False)))
cmp(C, 100)
a=near([c for _,c in C])
for x in a: print(x.split(" || actions ")[1].split(";")[-2:])
