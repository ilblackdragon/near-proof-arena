#!/usr/bin/env python3
"""F-2/F-3: the `rt` leaves' public boundary pair, from lane I's driver plan (`t1.py run` → plan.json).

`pair(plan, template, code_hash)` returns the in / out records of the plan's `RT enter` or
`RT resume` cut as `BndRec.encode` bytes (lane I's `bndrec.py`, cross-checked there against Lean's
`BndRec.encode`), one byte per public value (`BndLay.lean`: `engF` 450 B, `callF` 834 B).

F-3 (lane E's M11i view, plan §3.5) changes three things relative to the plan (run4, pre-M11i):
* `outRcptAcc` in an engine / call state is the **singleton** `[chainD enc outgoing]`
  (`ViewE.outDE (.eng a)`, plan §3.5 G-3 item 2); the plan has the empty list, so the singleton
  holds the plan's placeholder digest `0^42`;
* `WasmBnd.gasLeft` (M11i, u64 after `fuel`; `0` on records the plan has without it);
* the `RT enter` output's Wasm part is **lane A's `.pre` record** (`fbBnd (q, .pre)`: every counter
  `0`, every digest `bdigest []`, the remainder digest `vmCtxDigest` = the plan's placeholder, and
  — S2 — `codeRoot = SHA-256(code) ‖ 0^10` from the code hash the receipt rows read); the plan put
  the Wasm *entry* record there (lane I's seam: PREP, `.pre → .ent`, is now a `wasm` leaf).
Every other field is the plan's, asserted equal; the digests therefore differ from the plan's and
are printed (`d_in`, `d_out`)."""
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "t1"))
import bndrec  # noqa: E402

HEXF = {n for n, k in bndrec.BND_FIELDS if k == "dig"}
WHEXF = {n for n, k in bndrec.WASM_FIELDS if k == "dig"}
ZERO42 = bytes(42)
EMPTY = hashlib.sha384(b"").digest()[:42]  # bdigest []


def from_json(j):
    r = dict(j)
    for n in HEXF:
        r[n] = bytes.fromhex(r[n])
    r["outRcptAcc"] = [bytes.fromhex(d) for d in r["outRcptAcc"]]
    if r["wasm"] is not None:
        w = dict(r["wasm"])
        for n in WHEXF:
            w[n] = bytes.fromhex(w[n])
        w.setdefault("gasLeft", 0)
        r["wasm"] = w
    return r


def f3(r):
    """The M11i record shape: singleton outgoing accumulator (placeholder digest if absent)."""
    r = dict(r)
    if not r["outRcptAcc"]:
        r["outRcptAcc"] = [ZERO42]
    assert len(r["outRcptAcc"]) == 1
    return r


def pre_record(vm_ctx, code_hash):
    """Lane A's `fbBnd (q, .pre)` with S2 (`EnterC.preRec`)."""
    assert len(code_hash) == 32 and len(vm_ctx) == 42
    w = {n: (EMPTY if k == "dig" else 0) for n, k in bndrec.WASM_FIELDS}
    w["vmCtxDigest"] = vm_ctx
    w["codeRoot"] = bytes(code_hash) + bytes(10)
    return w


def pair(plan_path, template, code_hash=None):
    p = json.load(open(plan_path))
    segs = p["segments"]
    i = [s["template"] for s in segs].index(template)
    b_in = f3(from_json(p["B_0"] if i == 0 else segs[i - 1]["B_out"]))
    b_out = f3(from_json(segs[i]["B_out"]))
    if template == "RT enter":
        assert code_hash is not None, "enter: the code hash (S2)"
        b_out["wasm"] = pre_record(b_out["wasm"]["vmCtxDigest"], code_hash)
    e_in, e_out = bndrec.encode(b_in), bndrec.encode(b_out)
    assert bndrec.decode(e_in) == b_in and bndrec.decode(e_out) == b_out, "BndRec round trip"
    d_in, d_out = bndrec.bdigest(e_in).hex(), bndrec.bdigest(e_out).hex()
    return b_in, b_out, e_in, e_out, d_in, d_out


def code_hash_of(run_path):
    """The receiver account's code hash in the Lean run (the `APRE` record, bytes 32..64)."""
    run = json.load(open(run_path))
    rc = run["receipts"][0]
    pre = bytes.fromhex(rc["before"]["recvAcct"]["encode"]) if "before" in rc else None
    assert pre is not None, "lean run: receiver account"
    return pre[32:64]


if __name__ == "__main__":
    ch = code_hash_of(sys.argv[2]) if len(sys.argv) > 2 else bytes(32)
    for t in ["RT enter", "RT resume"]:
        _, _, a, b, di, do = pair(sys.argv[1], t, ch)
        print(t, len(a), len(b), di[:16], do[:16])
