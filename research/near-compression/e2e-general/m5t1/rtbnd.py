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
are printed (`d_in`, `d_out`).

F-4 (`resume_f4`, `pair(..., run=LEAN_RUN)`): the `RT resume` pair in lane E's M12 / lane F's F-4
shape (`BndLay.rbCons`, `resRule`): `B_in.vmAcc = bdigest []` (the call tape `K = []`), the input
accumulators are the Lean run's `chainD Ser.enc` of the outcomes / outgoing receipts before the
receipt; `B_out`: `receiptIdx + 1`, `rPrepaid = rBurnt = rUsed = 0`, `vmAcc = bdigest []`, the
accumulators after the receipt (one SHA-384 append each, asserted), and the copied fields
(`claimDigest`, `blockIdx`, `actionIdx`, `t`, `ctxRoot`, `outRcptN`, `proposalsAcc`, `bwAcc`) forced
to `B_in`'s (each override of the plan printed). `stRoot` out stays the plan's (lane B's `STC`
answers it on `STMA`; not copied; lane I's plan has a placeholder equal to `B_in.stRoot`, so the T1 stand-in
answers `bdigest("lane-F F-4 stand-in STC r_out" ‖ r_in)`)."""
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


COPIED = ["claimDigest", "blockIdx", "actionIdx", "t", "ctxRoot", "proposalsAcc", "bwAcc"]


def resume_f4(b_in, b_out, run_path):
    """F-4: the resume pair in the M12 / F-4 shape (module doc)."""
    rc = json.load(open(run_path))["receipts"]
    assert len(rc) == 1, "one receipt per resume segment"
    bef, aft = rc[0]["before"], rc[0]["after"]
    b_in, b_out = dict(b_in), dict(b_out)
    b_in["vmAcc"] = EMPTY
    b_in["outcomeAcc"] = bytes.fromhex(bef["outcomesChain"])
    b_in["outRcptAcc"] = [bytes.fromhex(bef["outgoingChain"])]
    for f in COPIED:
        if b_out[f] != b_in[f]:
            print(f"rtbnd F-4: B_out.{f} forced to B_in's (plan: {b_out[f]!r:.40} -> {b_in[f]!r:.40})")
        b_out[f] = b_in[f]
    if b_out["stRoot"] == b_in["stRoot"]:
        # lane I's plan carries a placeholder `stRoot` (equal in and out); lane B's `STC` does not
        # exist yet, so the T1 stand-in (`XTAPE`) answers a labelled stand-in root on `STMA`
        b_out["stRoot"] = bndrec.bdigest(b"lane-F F-4 stand-in STC r_out" + b_in["stRoot"])
        print("rtbnd F-4: B_out.stRoot = stand-in STC answer (plan's is B_in's placeholder)")
    b_out["receiptIdx"] = b_in["receiptIdx"] + 1
    b_out["rPrepaid"] = b_out["rBurnt"] = b_out["rUsed"] = 0
    b_out["vmAcc"] = EMPTY
    b_out["outcomeAcc"] = bytes.fromhex(aft["outcomesChain"])
    b_out["outRcptAcc"] = [bytes.fromhex(aft["outgoingChain"])]
    items = (bytes.fromhex(aft["outcomes"][-1]["ser"]), bytes.fromhex(aft["outgoing"][-1]["ser"]))
    assert len(aft["outcomes"]) == len(bef["outcomes"]) + 1 and len(aft["outgoing"]) == len(bef["outgoing"]) + 1
    assert bndrec.bdigest(b_in["outcomeAcc"] + items[0]) == b_out["outcomeAcc"], "outcome append"
    assert bndrec.bdigest(b_in["outRcptAcc"][0] + items[1]) == b_out["outRcptAcc"][0], "outgoing append"
    return b_in, b_out, items


CHAIN_CUTS = {"RT enter": (2, 3), "RT resume": (6, 7)}


def pair_chain(ch, template, code_hash=None, run=None):
    """F-5: the pair **is** lane I's chain (`chain.py plan` → chain.json, the cut records `c0 … c10`
    in lane E's current conventions): `RT enter` = c2 → c3, `RT resume` = c6 → c7 (located by the
    chain's own leaf table). Nothing is overridden; the leaf's conventions are asserted instead
    (enter: S2 `codeRoot`; resume: `vmAcc = bdigest []` in and out, `receiptIdx + 1`, the copied
    fields, `rPrepaid = rBurnt = rUsed = 0` out, one SHA-384 append per accumulator with the Lean
    run's `Ser.enc` items, the input Wasm part = lane A's fin record shape)."""
    lv = {x["leaf"]: (int(x["in"][1:]), int(x["out"][1:])) for x in ch["leaves"]}
    a, b = lv.get(template, CHAIN_CUTS[template])
    assert (a, b) == CHAIN_CUTS[template], f"chain: {template} spans c{a} -> c{b}"
    b_in, b_out = from_json(ch["cuts"][a]), from_json(ch["cuts"][b])
    assert len(b_in["outRcptAcc"]) == 1 and len(b_out["outRcptAcc"]) == 1, "singleton outRcptAcc"
    items = None
    if template == "RT enter":
        assert b_in["wasm"] is None and b_out["wasm"] is not None
        if code_hash is not None:
            assert b_out["wasm"]["codeRoot"] == bytes(code_hash) + bytes(10), "S2: codeRoot = code hash ‖ 0^10"
        w = pre_record(b_out["wasm"]["vmCtxDigest"], b_out["wasm"]["codeRoot"][:32])
        assert b_out["wasm"] == w, "enter: the .pre record"
        assert all(b_out[f] == b_in[f] for f in COPIED + ["receiptIdx", "stRoot", "outcomeAcc", "outRcptAcc", "vmAcc"])
    else:
        assert b_in["wasm"] is not None and b_out["wasm"] is None
        assert b_in["wasm"] == fin_record(b_in["wasm"]["vmCtxDigest"]), "resume: B_in.wasm = lane A's fin record"
        assert b_in["vmAcc"] == EMPTY and b_out["vmAcc"] == EMPTY, "vmAcc = bdigest []"
        assert all(b_out[f] == b_in[f] for f in COPIED), "copied fields"
        assert b_out["receiptIdx"] == b_in["receiptIdx"] + 1
        assert b_out["rPrepaid"] == b_out["rBurnt"] == b_out["rUsed"] == 0
        if run is not None:
            rc = json.load(open(run))["receipts"]
            assert len(rc) == 1, "one receipt per resume segment"
            bef, aft = rc[0]["before"], rc[0]["after"]
            assert b_in["outcomeAcc"].hex() == bef["outcomesChain"] and b_in["outRcptAcc"][0].hex() == bef["outgoingChain"]
            assert b_out["outcomeAcc"].hex() == aft["outcomesChain"] and b_out["outRcptAcc"][0].hex() == aft["outgoingChain"]
            items = (bytes.fromhex(aft["outcomes"][-1]["ser"]), bytes.fromhex(aft["outgoing"][-1]["ser"]))
            assert bndrec.bdigest(b_in["outcomeAcc"] + items[0]) == b_out["outcomeAcc"], "outcome append"
            assert bndrec.bdigest(b_in["outRcptAcc"][0] + items[1]) == b_out["outRcptAcc"][0], "outgoing append"
    e_in, e_out = bndrec.encode(b_in), bndrec.encode(b_out)
    assert bndrec.decode(e_in) == b_in and bndrec.decode(e_out) == b_out, "BndRec round trip"
    d_in, d_out = bndrec.bdigest(e_in).hex(), bndrec.bdigest(e_out).hex()
    assert (d_in, d_out) == (ch["digests"][a], ch["digests"][b]), "digests = the chain's"
    return b_in, b_out, e_in, e_out, d_in, d_out


def fin_record(vm_ctx):
    """Lane A's `fbBnd (q, .fin r)` (A-T5's halting out-record; `wasm_fin` in lane I's chain):
    every counter 0, every digest `bdigest []` (`fbCode` = `bdigest []` off `.pre`), the remainder
    digest `vmCtxDigest` as given."""
    w = {n: (EMPTY if k == "dig" else 0) for n, k in bndrec.WASM_FIELDS}
    w["vmCtxDigest"] = vm_ctx
    return w


def is_chain(path):
    return "cuts" in json.load(open(path))


def pair(plan_path, template, code_hash=None, run=None):
    p = json.load(open(plan_path))
    if "cuts" in p:
        return pair_chain(p, template, code_hash, run)
    segs = p["segments"]
    i = [s["template"] for s in segs].index(template)
    b_in = f3(from_json(p["B_0"] if i == 0 else segs[i - 1]["B_out"]))
    b_out = f3(from_json(segs[i]["B_out"]))
    if template == "RT enter":
        assert code_hash is not None, "enter: the code hash (S2)"
        b_out["wasm"] = pre_record(b_out["wasm"]["vmCtxDigest"], code_hash)
    if template == "RT resume" and run is not None:
        b_in, b_out, _ = resume_f4(b_in, b_out, run)
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
