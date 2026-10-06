#!/usr/bin/env python3
"""Scripted host-function edge cases (limits and deep success paths), harness `full` mode.

  host_edges.py  →  `<prepaid> <hex> <opts>` lines
"""
from wasmenc import *

GAS = 300 * 10**12
U64MAX = 2**64 - 1
SIG = {}
import json, os
INV = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                  "../../../docs/research/near-wasm-boundary-inventory.json")))
for i in INV["imports"]:
    if i["module"] == "env":
        SIG[i["name"]] = ([{"u64": I64, "u32": I32}[a.split(":")[1].strip()] for a in i["args"].split(",") if a.strip()],
                          [{"u64": I64, "u32": I32}[x.strip()] for x in i["returns"].split(",") if x.strip()])


class P:
    def __init__(self, data=b"", opts="rcv="):
        self.m = Module()
        self.m.vr = self.m.import_func("env", "value_return", [I64, I64], [])
        self.imp = {"value_return": self.m.vr}
        self.m.memory = (1, None)
        if data:
            self.m.datas.append(b"\x00" + i32c(0) + b"\x0b" + vec([bytes([x]) for x in data]))
        self.body = bytearray()
        self.opts = opts

    def call(self, name, *args, keep=False):
        if name not in self.imp:
            ps, rs = SIG[name]
            self.imp[name] = self.m.import_func("env", name, ps, rs)
        ps, rs = SIG[name]
        for v, t in zip(args, ps):
            self.body += i64c(v) if t == I64 else i32c(v)
        self.body += b"\x10" + uleb(self.imp[name])
        if rs and not keep:
            self.body += b"\x1a"
        return self

    def raw(self, b):
        self.body += b
        return self

    def done(self, ret=(0, 64)):
        self.body += i64c(ret[1]) + i64c(ret[0]) + b"\x10" + uleb(self.m.vr)
        self.m.func([], [], [], bytes(self.body))
        self.m.exports.append(("main", 0, len(self.m.imports)))
        return f"{GAS} {self.m.encode().hex()} {self.opts}"


cases = []
A = b"bob.near"
# logs
p = P(b"hello")
for _ in range(101):
    p.call("log_utf8", 5, 0)
cases.append(p.done())
p = P(b"x" * 6000)
for _ in range(3):
    p.call("log_utf8", 6000, 0)
cases.append(p.done())
cases.append(P(b"x" * 20000).call("log_utf8", U64MAX, 0).done())
cases.append(P(b"x" * 20000).call("log_utf8", 16385, 0).done())
cases.append(P("ab".encode("utf-16-le") * 5000).call("log_utf16", U64MAX, 0).done())
cases.append(P(b"z" * 16384).call("log_utf8", 16384, 0).call("log_utf8", 1, 0).done())
# storage
cases.append(P(b"k" * 3000).call("storage_write", 2049, 0, 10, 0, 0).done())
cases.append(P(b"k" * 3000).call("storage_write", 2048, 0, 10, 0, 0).done())
cases.append(P(b"v").call("storage_write", 1, 0, 4194305, 0, 0).done())
p = P(b"keyvalue" + bytes(5000))
p.call("storage_write", 3, 0, 5000, 8, 0).call("storage_write", 3, 0, 5, 3, 1)
p.call("storage_read", 3, 0, 2).call("register_len", 2).call("storage_has_key", 3, 0)
p.call("storage_remove", 3, 0, 3).call("storage_has_key", 3, 0).call("read_register", 1, 100)
cases.append(p.done((100, 64)))
p = P(b"key" + bytes(4001))
p.call("storage_write", 3, 0, 4001, 3, 0).call("storage_read", 3, 0, 1).call("storage_read", U64MAX, 0, 2)
cases.append(p.done())
# registers
p = P(b"r")
for i in range(101):
    p.call("write_register", i, 1, 0)
cases.append(p.done())
p = P(b"r")
for i in range(100):
    p.call("write_register", i, 1, 0)
p.call("write_register", 5, 1, 0)
cases.append(p.done())
# promises
# promise_and joint, then actions on joint
mem = A + (0).to_bytes(8, "little") + (1).to_bytes(8, "little")
p = P(mem)
p.call("promise_batch_create", 8, 0).call("promise_batch_create", 8, 0).call("promise_and", 8, 2)
p.call("promise_batch_action_create_account", 2)
cases.append(p.done())
p = P(mem)
p.call("promise_batch_create", 8, 0).call("promise_batch_create", 8, 0).call("promise_and", 8, 2)
p.call("promise_return", 2)
cases.append(p.done())
p = P(mem)
p.call("promise_batch_create", 8, 0).call("promise_batch_create", 8, 0).call("promise_and", 8, 2)
p.call("promise_batch_then", 2, 8, 0).call("promise_set_refund_to", 2, 8, 0)
cases.append(p.done())
p = P(mem)
p.call("promise_batch_create", 8, 0).call("promise_return", 0)
cases.append(p.done())
idx = b"".join((0).to_bytes(8, "little") for _ in range(129))
p = P(A + idx)
p.call("promise_batch_create", 8, 0).call("promise_and", 8, 129)
cases.append(p.done())
p = P(A + idx)
p.call("promise_batch_create", 8, 0).call("promise_and", 8, 128).call("promise_batch_then", 1, 8, 0)
cases.append(p.done())
p = P(A)
p.call("promise_batch_create", 8, 0).call("promise_batch_action_deploy_contract", 0, 4194305, 0)
cases.append(p.done())
p = P(A + b"\x00asm\x01\x00\x00\x00")
p.call("promise_batch_create", 8, 0).call("promise_batch_action_deploy_contract", 0, 8, 8)
p.call("promise_batch_action_transfer", 0, 40).call("promise_batch_action_create_account", 0)
cases.append(p.done())
# implicit receivers for transfer fees
for acct in [b"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", b"0x" + b"ab" * 20,
             b"0s" + b"cd" * 20, b"alice.near"]:
    p = P(acct + (5).to_bytes(16, "little"))
    p.call("promise_batch_create", len(acct), 0).call("promise_batch_action_transfer", 0, len(acct))
    cases.append(p.done())
# yield / resume success
p = P(b"cb" + b"payload")
p.call("promise_yield_create", 2, 0, 7, 2, 10**12, 1, 0).call("read_register", 0, 200)
p.call("promise_yield_resume", 32, 200, 7, 2).call("promise_yield_resume", 32, 300, 7, 2)
cases.append(p.done((200, 64)))
p = P(b"cb" + bytes(range(32)) + (0).to_bytes(16, "little"))
p.call("promise_yield_create_with_id", 2, 0, 0, 0, 34, 10**12, 0, 32, 2)
p.call("promise_yield_create_with_id", 2, 0, 0, 0, 34, 10**12, 0, 32, 2)
p.call("promise_yield_resume_with_yield_id", 32, 2, 1, 0).call("promise_yield_resume_with_yield_id", 32, 0, 1, 0)
cases.append(p.done())
# state init entries
p = P(A + bytes(32) + (0).to_bytes(16, "little") + b"kv")
p.call("promise_batch_create", 8, 0).call("promise_batch_action_state_init", 0, 32, 8, 40, keep=True)
p.raw(b"\x1a")
p.call("set_state_init_data_entry", 0, 1, 1, 56, 1, 57).call("set_state_init_data_entry", 0, 1, 1, 56, 1, 57)
cases.append(p.done())
p = P(A + bytes(32) + (0).to_bytes(16, "little") + b"kv")
p.call("promise_batch_create", 8, 0).call("set_state_init_data_entry", 0, 0, 1, 56, 1, 57)
cases.append(p.done())
# promise results via register
cases.append(P(b"", "results=S0102030405,F,N").call("promise_result", 0, 3).call("read_register", 3, 0).done())
cases.append(P(b"", "results=S01,F,N").call("promise_result", 1, 3).call("promise_result", 2, 3)
             .call("promise_results_count").done())
# abort
msg = "boom".encode("utf-16-le")
fil = "f.ts".encode("utf-16-le")
blob = len(msg).to_bytes(4, "little") + msg + len(fil).to_bytes(4, "little") + fil
cases.append(P(blob).call("abort", 4, 4 + len(msg) + 4, 7, 9).done())
cases.append(P(b"\x05\x00\x00\x00abcde").call("abort", 4, 4, 1, 1).done())
cases.append(P(b"").call("panic_utf8", 3, 0).done())
cases.append(P("ünïcödé\n\"q\"".encode()).call("panic_utf8", len("ünïcödé\n\"q\"".encode()), 0).done())
# value_return to many receivers, large
cases.append(P(b"", "rcv=alice.near,bob.near,carol.near").done((0, 4096)))
for c in cases:
    print(c)

# ed25519_verify on nearcore-judged vectors (oracle/fixtures/v3/ed25519), plus length errors
import glob
vecs = []
for f in sorted(glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../fixtures/v3/ed25519/*.jsonl"))):
    if "sha512" in f:
        continue
    for line in open(f):
        v = json.loads(line)
        if "sig" in v and "pk" in v and "msg" in v:
            vecs.append(v)
for v in vecs[:400]:
    sig, pk, msg = bytes.fromhex(v["sig"]), bytes.fromhex(v["pk"]), bytes.fromhex(v["msg"])
    p = P(sig + pk + msg)
    # store the verdict at memory[4000] and return it
    p.raw(i32c(4000))
    p.call("ed25519_verify", len(sig), 0, len(msg), len(sig) + len(pk), len(pk), len(sig), keep=True)
    p.raw(b"\x37\x03\x00")
    print(p.done((4000, 8)))
