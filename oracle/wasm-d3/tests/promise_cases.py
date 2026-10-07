#!/usr/bin/env python3
"""Promise and data-receiver families (requirements v0.2 §2.2; review F1, F4(e)).

  promise_cases.py N SEED  →  `<prepaid> <hex> [<receivers>]` lines

* `window`: create a promise (to alice.near / bob.near), attach gas G with
  `promise_batch_action_function_call`, then run one long pure range and run out of gas inside it. prepaid
  is calibrated from a full-gas nearcore run so that out-of-gas lands at a random point of the range
  (review F1: nearcore charges the *whole* range once promise gas lowers the limit).
* `errors`: invalid account ids (too short/long, bad chars, separators, non-UTF-8), empty method name,
  invalid promise index, amount over balance, the 1-yocto deposit, register-path arguments, OOB pointers,
  more than 1,024 promises.
* `receivers`: `value_return` with 1–3 output data receivers (sir and not-sir per-byte fees).
"""
import os
import random
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../tools"))
from harness_io import run_lines
from wasmenc import *

OP = 822756
HARNESS = os.environ.get("D3_HARNESS", "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")


def promise_module(acct, method, args, amount, gas, n_pure, n_promises=1, idx_override=None, reg_method=False):
    m = Module()
    m.vr = m.import_func("env", "value_return", [I64, I64], [])
    pc = m.import_func("env", "promise_batch_create", [I64, I64], [I64])
    fc = m.import_func("env", "promise_batch_action_function_call", [I64] * 7, [])
    m.memory = (1, None)
    blob = acct + method + args + amount.to_bytes(16, "little")
    m.datas.append(b"\x00" + i32c(0) + b"\x0b" + vec([bytes([x]) for x in blob]))
    a_off, m_off, g_off, amt_off = 0, len(acct), len(acct) + len(method), len(acct) + len(method) + len(args)
    body = bytearray()
    for _ in range(n_promises):
        body += i64c(len(acct)) + i64c(a_off) + b"\x10" + uleb(pc) + b"\x21\x00"   # local0 = idx
    idx = (b"\x20\x00" if idx_override is None else i64c(idx_override))
    mlen = -1 if reg_method else len(method)
    body += idx + i64c(mlen) + i64c(m_off) + i64c(len(args)) + i64c(g_off) + i64c(amt_off) + i64c(gas)
    body += b"\x10" + uleb(fc)
    for k in range(n_pure):
        body += i32c(k) + b"\x21\x01"
    m.func([], [], [(1, I64), (1, I32)], bytes(body))
    m.exports.append(("main", 0, len(m.imports)))
    return m.encode()


def receivers_module(nbytes):
    m = base_module()
    m.func([], [], [], value_return_tail(m, nbytes, 0))
    m.exports.append(("main", 0, len(m.imports)))
    return m.encode()


def run_near(lines):
    return run_lines([HARNESS], lines)


def main():
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    r = random.Random(seed)
    out = []
    # window family, calibrated
    nwin = n // 2
    specs = []
    for _ in range(nwin):
        acct = r.choice([b"alice.near", b"bob.near"])
        G = r.choice([0, 1, 10**12, 10**14, 2 * 10**14])
        n_pure = r.randrange(100, 3000)
        w = promise_module(acct, b"f", b"", r.choice([0, 0, 1, 10**20]), G, n_pure)
        specs.append((w, n_pure))
    full = run_near([f"{3 * 10**14} {w.hex()}" for w, _ in specs])
    for (w, n_pure), line in zip(specs, full):
        p = line.split(" ")
        if p[0] != "ok":
            out.append(f"{3 * 10**14} {w.hex()}")
            continue
        used = int(p[2])
        U = used - 2 * n_pure * OP          # used before the pure range (2 ops per iteration)
        k = r.choice([r.randrange(0, 2 * n_pure + 2), 0, 1, 2 * n_pure - 1, 2 * n_pure])
        out.append(f"{max(U + k * OP + r.randrange(0, OP), 0)} {w.hex()}")
    # error family
    bad_accts = [b"a", b"x" * 65, b"Alice.near", b"alice..near", b".alice", b"alice-", b"\xff\xfe",
                 b"al ice", b"alice_bob-c.near", b"x" * 64, b"ab"]
    for _ in range(n // 4):
        c = r.random()
        if c < 0.3:
            w = promise_module(r.choice(bad_accts), b"f", b"", 0, 10**12, 10)
        elif c < 0.4:
            w = promise_module(b"bob.near", b"", b"", 0, 10**12, 10)
        elif c < 0.5:
            w = promise_module(b"bob.near", b"f", b"", 0, 10**12, 10, idx_override=r.choice([1, 7, 2**63]))
        elif c < 0.6:
            w = promise_module(b"bob.near", b"f", b"", r.choice([10**24, 10**24 + 1, 2**127]), 10**12, 10)
        elif c < 0.7:
            w = promise_module(b"bob.near", b"f", b"", 0, 10**12, 10, reg_method=True)
        elif c < 0.8:
            w = promise_module(b"bob.near", b"f", b"", 0, r.choice([10**15, 2**64 - 1, 3 * 10**14]), 10)
        elif c < 0.9:
            w = promise_module(b"bob.near", b"meth" * r.randrange(1, 50), bytes(r.randrange(0, 200)), 1,
                               10**12, 10, n_promises=r.choice([1, 2, 1024, 1025]))
        else:
            w = promise_module(b"alice.near", b"f", bytes(r.randrange(0, 2000)), 0, 10**13, 10)
        out.append(f"{r.choice([3 * 10**14, 10**13, int(10 ** r.uniform(11, 13))])} {w.hex()}")
    # receivers family
    while len(out) < n:
        nb = r.choice([0, 1, 8, 100, 4096, 65536])
        rec = ",".join(r.choice(["alice.near", "bob.near", "carol.near"]) for _ in range(r.randrange(1, 4)))
        gas = r.choice([3 * 10**14, int(10 ** r.uniform(9.5, 13))])
        out.append(f"{gas} {receivers_module(nb).hex()} {rec}")
    r.shuffle(out)
    print("\n".join(out))


if __name__ == "__main__":
    main()
