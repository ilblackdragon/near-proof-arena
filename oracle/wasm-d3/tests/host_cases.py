#!/usr/bin/env python3
"""Host-function family for the D3α checkpoint-3 difftest.

  host_cases.py N SEED  →  `<prepaid> <hex> <opts>` lines (opts: harness `k=v;…`)

Each contract imports a random subset of the D3α host functions (signatures from the checked
inventory JSON) and calls 1–12 of them in sequence with arguments chosen by parameter name: lengths
and pointers into a data segment of interesting blobs (valid/invalid account ids, public keys, UTF-8
and UTF-16 strings incl. invalid and NUL-terminated ones, method-name lists, data ids, u128 amounts),
the register path (`len = u64::MAX`), out-of-bounds pointers, huge lengths, register ids, promise
indices. Results are stored to memory; `main` ends with `value_return` of a window, and contexts vary
input, promise results, attached deposit, balance and output data receivers. Run in harness mode
`full` (compute usage, logs, action log and the mock storage are compared too).
"""
import json
import os
import random
import sys
from wasmenc import *

HERE = os.path.dirname(os.path.abspath(__file__))
INV = json.load(open(os.path.join(HERE, "../../../docs/research/near-wasm-boundary-inventory.json")))
OOD = {"alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check", "ecrecover", "p256_verify"}
HOSTS = []
for i in INV["imports"]:
    if i["module"] != "env" or not i["enabled_in_production"] or i["name"] in OOD or i["name"].startswith("bls12381"):
        continue
    args = [(a.split(":")[0].strip(), a.split(":")[1].strip()) for a in i["args"].split(",") if a.strip()]
    rets = [r.strip() for r in i["returns"].split(",") if r.strip()]
    HOSTS.append((i["name"], args, rets))
T = {"u64": I64, "u32": I32}
MEM = 1024 * 65536
U64MAX = 2**64 - 1

# ---- blobs in the data segment (offset, bytes)
BLOBS = {}
_data = bytearray()


def blob(kind, b):
    BLOBS.setdefault(kind, []).append((len(_data), len(b)))
    _data.extend(b)


for a in [b"bob.near", b"alice.near", b"carol.near",
          b"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", b"0x" + b"ab" * 20,
          b"0s" + b"cd" * 20]:
    blob("acct", a)
for a in [b"a", b"Bob.near", b"x" * 65, b"aa..b", b"\xff\xfe"]:
    blob("badacct", a)
for pk in [b"\x00" + bytes(range(32)), b"\x01" + bytes(64), b"\x00" + bytes(range(1, 33))]:
    blob("pk", pk)
for pk in [b"\x00" + bytes(31), b"\x07" + bytes(32), b"\x00" + bytes(33)]:
    blob("badpk", pk)
for s in ["hello", "héllo wörld", "", "x" * 300, "tab\there \"q\" \\ \n"]:
    blob("utf8", s.encode())
blob("utf8", b"\xc3\x28bad")
blob("utf8z", b"null-terminated\x00")
blob("utf8z", b"\xe2\x82\xac euro\x00")
for s in ["hi", "π≈3", "😀"]:
    blob("utf16", s.encode("utf-16-le"))
blob("utf16", b"\x00\xd8\x41\x00")          # unpaired high surrogate
blob("utf16", b"abc")                       # odd length
blob("utf16z", "nul16".encode("utf-16-le") + b"\x00\x00")
for m in [b"foo", b"foo,bar", b",foo", b"foo,,bar", b"", b"m" * 40]:
    blob("names", m)
for d in [bytes.fromhex("af5570f5a1810b7af78caf4bc70a660f0df51e42baf91d4de5b2328de0e83dfc"), bytes(32), bytes(31)]:
    blob("dataid", d)           # first entry: the mock's first data id = sha256(0u64 le)
for amt in [0, 1, 10**24, 10**24 + 1, 2**127, 12345]:
    blob("u128", amt.to_bytes(16, "little"))
for pl in [b"", b"payload", bytes(1024), bytes(1025)]:
    blob("bytes", pl)
blob("code", b"\x00asm\x01\x00\x00\x00")
# abort(): u32 length prefix before UTF-16 string
for s in ["boom", "file.ts"]:
    e = s.encode("utf-16-le")
    blob("abortstr", len(e).to_bytes(4, "little") + e)
blob("u64s", b"".join(i.to_bytes(8, "little") for i in [0, 1, 2]))
blob("u64s", b"".join(i.to_bytes(8, "little") for i in [0, 9]))
DATA = bytes(_data)
WRITE = 8192    # scratch area for host outputs


def pick(r, kinds):
    k = r.choice(kinds)
    return r.choice(BLOBS[k])


def ptr_len(r, pname):
    """(len, ptr) for a `*_len`/`*_ptr` pair, by parameter role."""
    if r.random() < 0.06:
        return U64MAX, r.randrange(0, 4)                 # register path
    if r.random() < 0.04:
        return r.choice([MEM, 2**40, 5]), r.choice([MEM - 2, 0])
    if "account" in pname or "receiver" in pname or "beneficiary" in pname:
        kinds = ["acct"] * 9 + ["badacct"]
    elif "public_key" in pname:
        kinds = ["pk"] * 6 + ["badpk"]
    elif "method_names" in pname:
        kinds = ["names"]
    elif "method_name" in pname:
        kinds = ["names", "utf8"]
    elif "data_id" in pname or "yield_id" in pname or "code_hash" in pname:
        kinds = ["dataid"]
    elif "payload" in pname or "arguments" in pname or "value" in pname or "key" in pname or "data" in pname:
        kinds = ["bytes", "utf8", "acct"]
    elif "code" in pname:
        kinds = ["code", "bytes"]
    elif pname in ("len",):
        kinds = ["utf8", "utf8", "utf16"]
    else:
        kinds = ["bytes", "utf8"]
    off, ln = pick(r, kinds)
    return ln, off


PROMISE_MAKERS = {"promise_create", "promise_then", "promise_batch_create", "promise_batch_then", "promise_and",
                  "promise_yield_create"}
STATE = {"np": 0}


def gen_call(r, name, args, m, imp):
    code = bytearray()
    vals = {}
    names = [a for a, _ in args]
    for pn, _ in args:
        if pn in vals:
            continue
        if pn.endswith("_len") and pn[:-4] + "_ptr" in names:
            ln, p = ptr_len(r, pn)
            if name in ("log_utf16",) and r.random() < 0.5:
                o, l = pick(r, ["utf16", "utf16z"])
                ln, p = (U64MAX if r.random() < 0.3 else l), o
            vals[pn], vals[pn[:-4] + "_ptr"] = ln, p
    for pn, _ in args:
        if pn in vals:
            continue
        if name in ("log_utf8", "panic_utf8", "log_utf16") and pn in ("len", "ptr"):
            kind = r.choice(["utf8", "utf8z"]) if name != "log_utf16" else r.choice(["utf16", "utf16z"])
            o, l = pick(r, [kind])
            vals["len"] = U64MAX if kind.endswith("z") else l
            vals["ptr"] = o
            continue
        if pn in ("ptr",) and name == "value_return":
            continue
        if pn == "register_id" or pn.endswith("register_id"):
            vals[pn] = r.choice([0, 1, 2, 3, 99, 2**33])
        elif pn == "action_index":
            vals[pn] = r.choice([0, 1, 2, 3, 2**40])
        elif pn in ("promise_idx", "promise_index"):
            np_ = STATE["np"]
            vals[pn] = r.randrange(np_) if np_ and r.random() < 0.92 else r.choice([0, 1, 5, 2**40])
        elif pn == "promise_idx_ptr":
            o, l = pick(r, ["u64s"])
            vals[pn], vals["promise_idx_count"] = o, l // 8 if r.random() < 0.9 else 200
        elif pn in ("amount_ptr", "allowance_ptr"):
            vals[pn] = pick(r, ["u128"])[0] if r.random() < 0.95 else MEM - 3
        elif pn in ("balance_ptr", "stake_ptr"):
            vals[pn] = WRITE + 16 * r.randrange(8) if r.random() < 0.95 else MEM - 8
        elif pn == "gas":
            vals[pn] = r.choice([0, 10**12, 10**14, 5 * 10**14, 2**64 - 1])
        elif pn == "gas_weight":
            vals[pn] = r.choice([0, 1, 7])
        elif pn == "num_nonces":
            vals[pn] = r.choice([0, 1, 4, 65535, 65536])
        elif pn == "nonce":
            vals[pn] = r.choice([0, 5, 2**63])
        elif pn == "result_idx":
            vals[pn] = r.choice([0, 1, 2, 3])
        elif pn in ("msg_ptr", "filename_ptr"):
            vals[pn] = r.choice([pick(r, ["abortstr"])[0] + 4, 2, 0])
        elif pn in ("line", "col"):
            vals[pn] = r.randrange(0, 100)
        elif pn == "opcodes":
            vals[pn] = r.choice([0, 1, 1000])
        elif pn == "value_len" and name == "value_return":
            pass
        elif pn == "data_ptr":
            vals[pn] = 0
        else:
            vals[pn] = r.randrange(0, 64)
    if name == "value_return":
        o, l = pick(r, ["bytes", "utf8"])
        vals["value_len"], vals["value_ptr"] = l, o
    for pn, ty in args:
        v = vals[pn]
        code += i64c(v) if T[ty] == I64 else i32c(v)
    code += b"\x10" + uleb(imp[name])
    if name in PROMISE_MAKERS:
        STATE["np"] += 1
    return code


def main():
    n, seed = int(sys.argv[1]), int(sys.argv[2])
    r = random.Random(seed)
    for _ in range(n):
        m = Module()
        m.vr = m.import_func("env", "value_return", [I64, I64], [])
        chosen = r.sample(HOSTS, r.randrange(3, 10))
        imp = {"value_return": m.vr}
        for name, args, rets in chosen:
            if name == "value_return":
                continue
            imp[name] = m.import_func("env", name, [T[t] for _, t in args], [T[t] for t in rets])
        m.memory = (1, None)
        m.datas.append(b"\x00" + i32c(0) + b"\x0b" + vec([bytes([x]) for x in DATA]))
        body = bytearray()
        slot = 0
        STATE["np"] = 0
        weights = [0.08 if c[0].startswith("storage_iter") else 1.0 for c in chosen]
        maker = [c for c in HOSTS if c[0] in ("promise_batch_create", "promise_create")]
        calls = r.choices(chosen, weights, k=r.randrange(1, 13))
        if r.random() < 0.6:
            mk = r.choice(maker)
            if mk[0] not in imp:
                imp[mk[0]] = m.import_func("env", mk[0], [T[t] for _, t in mk[1]], [T[t] for t in mk[2]])
            calls.insert(0, mk)
        for name, args, rets in calls:
            if name == "value_return" and r.random() < 0.5:
                continue
            body += gen_call(r, name, args, m, imp)
            if rets:
                # store the result: tee into a local, store it
                body += (b"\x21\x00" if rets[0] == "u64" else b"\x21\x01")
                body += i32c(WRITE + 256 + 8 * slot) + (b"\x20\x00\x37\x03\x00" if rets[0] == "u64" else b"\x20\x01\x36\x02\x00")
                slot += 1
        body += i64c(256 + 8 * slot + 128) + i64c(WRITE) + b"\x10" + uleb(m.vr)
        m.func([], [], [(1, I64), (1, I32)], bytes(body))
        m.exports.append(("main", 0, len(m.imports)))
        opts = []
        if r.random() < 0.4:
            opts.append("input=" + bytes(r.getrandbits(8) for _ in range(r.randrange(0, 40))).hex())
        if r.random() < 0.4:
            opts.append("results=" + ",".join(r.choice(["S" + bytes(r.randrange(0, 9)).hex(), "F", "N"])
                                              for _ in range(r.randrange(0, 4))))
        if r.random() < 0.3:
            opts.append(f"deposit={r.choice([0, 1, 10**24])}")
        if r.random() < 0.2:
            opts.append(f"balance={r.choice([0, 1, 10**20])}")
        if r.random() < 0.3:
            opts.append("rcv=" + ",".join(r.choice(["alice.near", "bob.near"]) for _ in range(r.randrange(1, 3))))
        gas = r.choice([3 * 10**14, 3 * 10**14, 10**13, int(10 ** r.uniform(10, 12.5))])
        print(gas, m.encode().hex(), ";".join(opts) or "rcv=")


if __name__ == "__main__":
    main()
