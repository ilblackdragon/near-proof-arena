#!/usr/bin/env python3
"""Lane I, I-2 (2026-11-25): T1's leaf chain under the current boundary conventions.

    chain.py inputs RUN_DIR [--lean-run LEAN_RUN.json] [--out data/t1-inputs.json]
    chain.py plan OUT_DIR [--inputs data/t1-inputs.json] [--no-lean] [--no-leaves]

`inputs` collects, from a `t1.py run` output directory (report / Lean outputs / calls / case) and
lane F's Lean engine dump (`m5t1-tool dump`: the outcome and outgoing-receipt `Ser.enc` items and
the receipt-state totals before / after the FunctionCall receipt), every value the chain needs,
into one JSON file (the committed `data/t1-inputs.json`; no deps needed to rebuild the chain).

`plan` builds the cut records `c0 … c10` (`BndRec`, lane E's `E2E/Boundary.lean`) as lane E's
concrete view `ViewE.viewE` defines them, encodes them with `bndrec.py` and checks every record
and the view constants against a Lean evaluation (`lean_check`), and compares each saved leaf's
public values with the cuts it spans (`leaf_table`). Writes `OUT/chain.json` and `OUT/chain.md`.

Conventions (plan §3.5 M11i, M12, M13 / "D-a – D-d", lane F F-4):
* M11i: `WasmBnd.gasLeft` (u64 after `fuel`); `outRcptAcc` is one chain (`[chainD enc rs]` in an
  engine / call state, `[]` at `init` / `done`); `B_0`: `ctxRoot = ctxD(.raw cb wb)` =
  `bdigest (0 ‖ u32be ℓ_B ‖ u32be |cb| ‖ cb ‖ wb)`, `stRoot = stD .none`,
  `outD .none = (bdigest [], [], bdigest [], bdigest [0])`, `vmAcc = bdigest []`.
* M12 `clearE`: `claimDigest = bdigest []`, `blockIdx = actionIdx = t = 0` everywhere; engine cuts
  carry `receiptIdx = |outcomes|`, `gasUsed = gasBurnt = rs.gas`, `balanceBurnt = rs.txBurnt`,
  `compute = rs.compute` (`start`: all 0); a call adds `rPrepaid`; resume outputs `receiptIdx + 1`
  and `rPrepaid = rBurnt = rUsed = 0`; `done H o` carries `o.gasUsed`, `o.balanceBurnt`, the rest 0.
* M13: the `start` cut commits lane B's `R_0` (`EngSt.ovl0`); the finalize step
  (`yields _ _ 0 → done out`) is its own STATE leaf (IF-FINAL); `W` = the whole `stRoot`.
  `rest`: lane E's `encRestI` is **not adopted** by lane B's default instance or lane F's leaves
  (both still carry a stand-in `rest`), so the driver keeps a `rest = 0^42` placeholder.
* S2 / A-T3: the enter output is lane A's `.pre` record (`fbBnd`: counters 0, digests
  `bdigest []`, `codeRoot = SHA-256(code) ‖ 0^10`); PREP (`.pre → .ent`) follows enter.
* F-4: accumulators are the Lean run's `chainD Ser.enc` (`acc' = bdigest (acc ‖ enc item)`).

Fields no component computes yet are `0^42` placeholders, each listed with its owner in
`PLACEHOLDERS`; a placeholder is the same value at every cut where the view's value is a constant
(`stD .none`) and changes nowhere else, so the chain holds digest for digest by construction and a
leaf's exposed value is compared with the view's value wherever the view's value is known.
"""
import argparse
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bndrec  # noqa: E402

DEPS = "/data/illia/nearproof-deps"
INPUTS = os.path.join(HERE, "data", "t1-inputs.json")
LEAN_RUN = os.environ.get("LEAN_RUN", f"{DEPS}/tmp-laneF/f4/lean-run.json")
ZERO = bndrec.ZERO
E = bndrec.bdigest(b"")                      # bdigest []


def tagd(i):
    """`bdigest [i]`: `outD`'s constructor tag (`.none` 0, `.eng` 1, `.done` 2)."""
    return bndrec.bdigest(bytes([i]))


def chain(items):
    """`View.chainD enc l` (`chainR enc l.reverse`): `[] ↦ bdigest []`, `l ++ [a] ↦ bdigest (chainD l ‖ enc a)`."""
    a = E
    for x in items:
        a = bndrec.bdigest(a + x)
    return a


def raw_pre(cb, wb, lb, order="big"):
    """`ViewE.rawPre lB cb wb = 0 ‖ u32 ℓ_B ‖ u32 |cb| ‖ cb ‖ wb` (`u32 = Bytes.beN 4`: big-endian).
    `order="little"` is lane G's INIT AIR (`m5d/tracegen.py` `u(n, 4)`)."""
    return b"\x00" + lb.to_bytes(4, order) + len(cb).to_bytes(4, order) + cb + wb


def st_commit(tag, ws, wslen, trie, idx, rest):
    """lane B's `StCommit.ser` (`[tag] ‖ ws(48) ‖ u64le wsLen ‖ trie(32) ‖ u64le idx ‖ rest(42)`, 139 B)."""
    assert len(ws) == 48 and len(trie) == 32 and len(rest) == 42
    return bndrec.bdigest(bytes([tag]) + ws + wslen.to_bytes(8, "little") + trie + idx.to_bytes(8, "little") + rest)


def root42(words):
    """A cached CODE / FUNC commitment (5 × u64 + 16 bits, lane A README §8) as 42 bytes: 5 big-endian
    u64 then the last word as a big-endian u16. **Lane I's packing**: lane A has not fixed one (the
    Lean `codeRootOf` is the stand-in `ccT1`), so this is a proposal, not a view value."""
    assert len(words) == 6 and words[5] < 2 ** 16
    return b"".join(w.to_bytes(8, "big") for w in words[:5]) + words[5].to_bytes(2, "big")


def dig48(limbs):
    """6 SHA-512 words as 3 limbs of 21 bits each (lane A `seg::wl`, lane B `root21`)."""
    return b"".join((limbs[3 * j] + (limbs[3 * j + 1] << 21) + (limbs[3 * j + 2] << 42)).to_bytes(8, "big")
                    for j in range(6))


def root16(v):
    return bytes(b for x in v for b in (x >> 8, x & 255))


def limbs3(v):
    return bytes(b for x in v for b in ((x >> 16) & 255, (x >> 8) & 255, x & 255))


# ---------------------------------------------------------------------------
# inputs
# ---------------------------------------------------------------------------
def seg_publics(pubs, R):
    """lane A's 105 segment public values → both sides (`t1.seg_bnd`)."""
    import t1
    return t1.seg_bnd(pubs, R)


def inputs_from(case, full, calls, comps, prep, lean_run, laneb_if=None):
    """Everything the chain needs, as JSON-able values (hex for bytes)."""
    import stmt
    cb = open(os.path.join(case, "claim.bin"), "rb").read()
    wb = open(os.path.join(case, "witness.bin"), "rb").read()
    b0, b1 = stmt.parse_claim(cb)["secB"]
    o = full["outputs"]
    st = comps["state"]["bnd"]
    ws = [c for c in comps["wasm-seg"]["calls"] if c.get("plan")]
    assert len(calls) == 1 and len(ws) == 1, "T1: one Wasm call"
    c = calls[0]
    rc = json.load(open(lean_run))["receipts"]
    assert len(rc) == 1, "T1: one FunctionCall receipt"
    rc = rc[0]

    def side(s):
        b = rc[s]
        return {"outcomes": [x["ser"] for x in b["outcomes"]], "outgoing": [x["ser"] for x in b["outgoing"]],
                "outcomesChain": b["outcomesChain"], "outgoingChain": b["outgoingChain"],
                "gas": int(b["gas"]), "compute": int(b["compute"]), "txBurnt": int(b["txBurnt"]),
                "nProposals": int(b["nProposals"]), "committed": b["committed"]}
    inp = {
        "case": os.path.basename(case.rstrip("/")),
        "claim_sha256": hashlib.sha256(cb).hexdigest(), "witness_sha256": hashlib.sha256(wb).hexdigest(),
        "lB": b1 - b0, "cb_len": len(cb),
        "ctx_raw_be": bndrec.bdigest(raw_pre(cb, wb, b1 - b0, "big")).hex(),
        "ctx_raw_le": bndrec.bdigest(raw_pre(cb, wb, b1 - b0, "little")).hex(),
        "prev_state_root": st["pre_root"], "wsLen": st["wsLen"],
        "post_state_root": o["stateRoot"], "gasUsed": int(o["gasUsed"]), "balanceBurnt": int(o["balanceBurnt"]),
        "computeUsage": int(o["computeUsage"]), "n_outcomes": len(o["outcomes"]),
        "n_outgoing": len(o["outgoingReceipts"]), "n_proposals": len(o["proposals"]),
        "call": {"method": c["method"], "prepaid": c["prepaid"], "code_sha256": c["code_sha256"], "steps": c["steps"],
                 "burnt": c["real"]["burnt"], "used": c["real"]["used"], "R": prep["regularOpCost"],
                 "stackRem": prep["stackRem"], "g0": prep["g0"], "gFinal": prep["gFinal"]},
        "segments": ws[0]["bnd"],
        "acc": {"before": side("before"), "after": side("after")},
    }
    if laneb_if:
        s = json.load(open(laneb_if))["statement"]
        inp["R_0"], inp["R_n"] = dig48(s[17:35]).hex(), dig48(s[35:53]).hex()
        assert root16(s[0:16]).hex() == st["pre_root"] and s[16] == st["wsLen"]
    done_digests(inp)
    return inp


def done_digests(inp):
    """G-5: `ctxD (.header H)`, `outD (.done o).1` of the done cut (lane E's view, ViewSer's fixed-width
    serialisers), Lean-evaluated by lane G's `m5d-tool dump` (M5D_DUMP); for T1's claim without the dump,
    the committed inputs' values."""
    m5d = os.environ.get("M5D_DUMP", f"{DEPS}/e2e-m5d/g5/t1f/dump.json")
    if os.path.exists(m5d):
        bo = json.load(open(m5d))["bout"]
        inp["ctx_header"], inp["out_done"] = bo["ctxHeaderD"], bo["outDoneD"]
    elif os.path.exists(INPUTS):
        fx = json.load(open(INPUTS))
        if fx.get("claim_sha256") == inp.get("claim_sha256") and fx.get("ctx_header"):
            inp["ctx_header"], inp["out_done"] = fx["ctx_header"], fx["out_done"]


LANEB_IF = f"{DEPS}/laneB-t1/t1b/T1S/if/out/statement.json"


def inputs_from_run(run_dir, lean_run=LEAN_RUN, laneb_if=LANEB_IF):
    rep = json.load(open(os.path.join(run_dir, "report.json")))
    full = json.load(open(os.path.join(run_dir, "lean-full.json")))
    calls = json.load(open(os.path.join(run_dir, "calls", "calls.json")))
    prep = json.load(open(calls[0]["prep"]))
    case = os.path.join(run_dir, "case") if os.path.exists(os.path.join(run_dir, "case", "claim.bin")) else rep["case"]
    inp = inputs_from(case, full, calls, rep["components"], prep, lean_run, laneb_if if os.path.exists(laneb_if) else None)
    inp["case"] = os.path.relpath(rep["case"], f"{DEPS}/corpora")
    return inp


# ---------------------------------------------------------------------------
# the chain
# ---------------------------------------------------------------------------
# fields no component computes yet: (cut field, view value, owner)
PLACEHOLDERS = [
    ("stRoot at init / done", "stD .none (lane B's default instance: a constant)", "B: publish the constant"),
    ("stRoot.rest at every engine / call cut", "bdigest (encRest (restOf v)) — encRestI (D-d) not adopted",
     "B (default instance) + F (resume STMQ/STMA metas) + E (encRestI)"),
    ("stRoot.ws at c2 (before receipt 1)", "working-set root after the 8 changes before receipt 1",
     "B: split the STATE segment at the RT cuts"),
    ("ctxRoot at engine / call cuts", "ctxD (.intake I) = bdigest (1 ‖ Ser.enc I)",
     "E: Ser Intake closure (ViewSer); G: INIT computes it (B_1)"),
    ("wasm.vmCtxDigest", "bdigest (encRest (.other (q, cc)) / (.air …))", "A (m6 §6; needs gasLeft + σ at host rows)"),
    ("wasm.fuel", "the call machine's n (fuel_out = fuel_in − Δt)", "A: expose fuel_in of segment 0 / PREP"),
    ("wasm.codeRoot / funcRoot packing", "codeC.root (codeRecs …) (stand-in ccT1 in Lean)",
     "A: fix the 42-B packing of the cached commitment (driver: 5 × u64be + u16be)"),
]


def wasm_pre(code_hash):
    """lane A's `fbBnd (q, .pre)` with S2 (= lane F's `EnterC.preRec`)."""
    w = {n: (E if k == "dig" else 0) for n, k in bndrec.WASM_FIELDS}
    w["vmCtxDigest"] = ZERO
    w["codeRoot"] = bytes.fromhex(code_hash) + bytes(10)
    return w


def wasm_fin():
    """lane A's `fbBnd (q, .fin r)`: every counter 0, every digest `bdigest []` (`fbCode` = `bdigest []`)."""
    w = {n: (E if k == "dig" else 0) for n, k in bndrec.WASM_FIELDS}
    w["vmCtxDigest"] = ZERO
    return w


def wasm_air(b, code_root, func_root, stack_rem):
    """lane A's `airBnd` from one side of a segment's public boundary: `pc`, `sp = sb`, frames /
    globals / registers = `ctxDigest[:42]`, `memRoot[:42]`, `memPages = nblk / 64`,
    `promisesDigest = bdigest []`, **`gasLeft = g`** (M11i target; lane A's `airBnd` still has the
    default 0), `stackRem` (honest, unbound), code / func roots (PREP's cached commitments)."""
    fd = bytes.fromhex(b["ctx"])[:42]
    return {"pc": b["pc"], "sp": b["sb"], "stackRem": stack_rem, "fuel": 0, "gasLeft": b["g"],
            "framesDigest": fd, "memRoot": bytes.fromhex(b["mem"])[:42], "memPages": b["nblk"] // 64,
            "globalsDigest": fd, "registersDigest": fd, "vmCtxDigest": ZERO, "promisesDigest": E,
            "codeRoot": code_root, "funcRoot": func_root}


def _rec(phase, **kw):
    r = bndrec.blank(E)             # claimDigest = bdigest [] (M12)
    r["phase"] = bndrec.PHASE[phase]
    r.update(proposalsAcc=E, vmAcc=E)
    r.update(kw)
    return r


def _eng_acc(side):
    oc = [bytes.fromhex(x) for x in side["outcomes"]]
    og = [bytes.fromhex(x) for x in side["outgoing"]]
    assert chain(oc).hex() == side["outcomesChain"] and chain(og).hex() == side["outgoingChain"], "chainD"
    assert side["nProposals"] == 0
    return dict(outcomeAcc=chain(oc), outRcptAcc=[chain(og)], proposalsAcc=chain([]), bwAcc=tagd(1))


def _eng_clear(side, n_out):
    return dict(receiptIdx=n_out, gasUsed=side["gas"], gasBurnt=side["gas"], balanceBurnt=side["txBurnt"],
                compute=side["compute"])


# the leaves: (name, lanes, cut in, cut out, what)
LEAVES = [
    ("INIT ⊕ IF", "G (INIT) ⊕ B (IF-INTAKE)", 0, 1, "init cb wb → eng I start (split leaf: CLM bytes + PSR join)"),
    ("STATE seg A", "B ⊕ F (engine rows)", 1, 2, "VM-free steps up to receipt 1's step (receipt 0, the 3 forwards)"),
    ("RT enter", "F", 2, 3, "eng I c → call I c [] q .pre"),
    ("PREP", "A", 3, 4, ".pre → .ent (cstep q .pre = preConf q)"),
    ("WASM seg 0", "A", 4, 5, "steps (0, 13]"),
    ("WASM seg 1", "A", 5, 6, "steps (13, 26], halts → .fin r"),
    ("RT resume", "F ⊕ B (STC)", 6, 7, "estepO (strictO [(q, r)]): refund, outcome, outgoing receipt"),
    ("STATE seg B", "B ⊕ F (engine rows)", 7, 8, "VM-free steps after receipt 1 → eng I ⟨yields _ _ 0⟩ (may be empty)"),
    ("finalize", "B (IF-FINAL) ⊕ F (engine rows)", 8, 9, "yields _ _ 0 → eng I ⟨done out⟩ (D-b: own STATE leaf)"),
    ("FINAL", "G ⊕ B (FINAL half)", 9, 10, "eng I ⟨done out⟩ → fin I out → done H o"),
]


def build(inp):
    """The cut records c0 … c10 (each a `BndRec` dict) and the per-field provenance notes."""
    acc_b, acc_a = inp["acc"]["before"], inp["acc"]["after"]
    call = inp["call"]
    segs = inp["segments"]
    assert len(segs) == 2, "T1 at k = 13: two segments"
    prev = bytes.fromhex(inp["prev_state_root"])
    wslen = inp["wsLen"]
    r0 = bytes.fromhex(inp["R_0"]) if inp.get("R_0") else bytes(48)
    rn = bytes.fromhex(inp["R_n"]) if inp.get("R_n") else bytes(48)
    st_none = ZERO
    code_root, func_root = bytes(42), bytes(42)
    if inp.get("prep"):
        code_root, func_root = root42(inp["prep"]["code_root_words"]), root42(inp["prep"]["func_root_words"])

    def st(tag, ws):
        return st_commit(tag, ws, wslen, prev, 0, ZERO)

    eng0 = dict(outcomeAcc=E, outRcptAcc=[E], proposalsAcc=E, bwAcc=tagd(1))
    c = [None] * 11
    c[0] = _rec("init", ctxRoot=bytes.fromhex(inp["ctx_raw_be"]), stRoot=st_none,
                outcomeAcc=E, outRcptAcc=[], proposalsAcc=E, bwAcc=tagd(0))
    c[1] = _rec("eng", ctxRoot=ZERO, stRoot=st(1, r0), **eng0)
    c[2] = _rec("eng", ctxRoot=ZERO, stRoot=st(1, bytes(48)), **_eng_acc(acc_b),
                **_eng_clear(acc_b, len(acc_b["outcomes"])))
    c[3] = dict(c[2], phase=bndrec.PHASE["call"], inCall=True, rPrepaid=call["prepaid"],
                wasm=wasm_pre(call["code_sha256"]))
    c[4] = dict(c[3], wasm=wasm_air(segs[0]["in"], code_root, func_root, call["stackRem"]))
    c[5] = dict(c[3], wasm=wasm_air(segs[0]["out"], code_root, func_root, call["stackRem"]))
    c[6] = dict(c[3], wasm=wasm_fin())
    c[7] = _rec("eng", ctxRoot=ZERO, stRoot=st(1, rn), **_eng_acc(acc_a),
                **_eng_clear(acc_a, len(acc_a["outcomes"])))
    c[8] = dict(c[7])
    c[9] = dict(c[7], stRoot=st(3, rn), receiptIdx=inp["n_outcomes"], gasUsed=inp["gasUsed"],
                gasBurnt=inp["gasUsed"], balanceBurnt=inp["balanceBurnt"], compute=inp["computeUsage"])
    # G-5: ctxD (.header H) = bdigest (3 ‖ Ser.enc H), outD (.done o).1 = bdigest (Ser.enc o) with ViewSer's
    # fixed-width Ser ChunkInner / Ser Outputs (Lean-evaluated by `m5d-tool dump`: inputs ctx_header / out_done)
    c[10] = _rec("done", ctxRoot=bytes.fromhex(inp["ctx_header"]) if inp.get("ctx_header") else ZERO, stRoot=st_none,
                 gasUsed=inp["gasUsed"], balanceBurnt=inp["balanceBurnt"],
                 outcomeAcc=bytes.fromhex(inp["out_done"]) if inp.get("out_done") else ZERO, outRcptAcc=[],
                 proposalsAcc=E, bwAcc=tagd(2))
    for r in c:
        if r["wasm"] is not None:
            r["wasm"] = dict(r["wasm"])
    return c


def check_conventions(c, inp):
    """The rules of the module doc, asserted on the records; returns the list of violations."""
    bad = []

    def need(cond, msg):
        if not cond:
            bad.append(msg)
    for i, r in enumerate(c):
        need(r["claimDigest"] == E and r["blockIdx"] == 0 and r["actionIdx"] == 0 and r["t"] == 0,
             f"c{i}: M12 constants (claimDigest = bdigest [], blockIdx = actionIdx = t = 0)")
        need(r["rBurnt"] == 0 and r["rUsed"] == 0, f"c{i}: rBurnt = rUsed = 0")
        need(r["inCall"] == (r["wasm"] is not None) == (r["phase"] == 6), f"c{i}: inCall = wasm.isSome = phase 6")
        need((r["rPrepaid"] != 0) == r["inCall"], f"c{i}: rPrepaid only inside a call")
        need(len(r["outRcptAcc"]) == (1 if r["phase"] in (1, 6) else 0), f"c{i}: outRcptAcc singleton in eng/call")
        need(r["bwAcc"] == tagd({0: 0, 1: 1, 6: 1, 4: 2}[r["phase"]]), f"c{i}: outD constructor tag")
        need(r["vmAcc"] == E, f"c{i}: vmAcc = vmD [] (K = [] at every T1 cut)")
    need(c[0]["phase"] == 0 and c[0]["gasUsed"] == 0 and c[0]["receiptIdx"] == 0, "B_0 clear fields 0")
    need(all(c[1][f] == 0 for f in ("receiptIdx", "gasUsed", "compute")), "start: clear0")
    need(c[7]["receiptIdx"] == c[6]["receiptIdx"] + 1, "resume: receiptIdx + 1")
    need(c[7]["rPrepaid"] == 0, "resume: rPrepaid = 0 out")
    need(c[3]["wasm"]["codeRoot"] == bytes.fromhex(inp["call"]["code_sha256"]) + bytes(10), "S2: .pre codeRoot")
    need(c[10]["phase"] == 4 and c[10]["gasUsed"] == inp["gasUsed"] and c[10]["balanceBurnt"] == inp["balanceBurnt"]
         and c[10]["receiptIdx"] == c[10]["compute"] == c[10]["gasBurnt"] == 0, "done: o.gasUsed / o.balanceBurnt, rest 0")
    need(c[7]["gasUsed"] == inp["gasUsed"] and c[7]["compute"] == inp["computeUsage"], "after receipt 1 = header totals")
    return bad


def digests(c):
    return [bndrec.digest(r).hex() for r in c]


def leaf_pairs(c, leaves=LEAVES):
    """Each leaf's `(h(B_in), h(B_out))`, each record encoded on its own."""
    return [(bndrec.digest(c[a]).hex(), bndrec.digest(c[b]).hex()) for _, _, a, b, _ in leaves]


def chain_ok(pairs, d0=None, dn=None):
    """Adjacent leaves chain digest for digest: `d_out(k) = d_in(k + 1)` (and the first input is
    `h(B_0)`, the last output `h(done)` when given). The plan's pairs chain by construction; the
    check matters for digests read off leaves."""
    return (all(pairs[i][1] == pairs[i + 1][0] for i in range(len(pairs) - 1))
            and (d0 is None or pairs[0][0] == d0) and (dn is None or pairs[-1][1] == dn))


# ---------------------------------------------------------------------------
# Lean cross-check: the records and the view constants
# ---------------------------------------------------------------------------
def lean_consts_source(inp, cb, wb):
    """A Lean program printing `ViewE.rawPre` (BE) on T1's bytes, `chainD id` of the accumulator
    items, `bdigest [i]` (i = 0, 1, 2) and `bdigest []` — lane E's own definitions."""
    a, b = inp["acc"]["before"], inp["acc"]["after"]
    lst = lambda xs: "[" + ", ".join(f'h "{x}"' for x in xs) + "]"  # noqa: E731
    exprs = [("ctx_raw_be", f'bdigest (NearSpecV3.E2E.ViewE.rawPre (fun _ => {inp["lB"]}) (h "{cb.hex()}") (h "{wb.hex()}"))'),
             ("u32_lB", f'NearSpecV3.E2E.ViewE.u32 {inp["lB"]}'),
             ("out_before", f'chainD (fun x => x) {lst(a["outcomes"])}'),
             ("rcpt_before", f'chainD (fun x => x) {lst(a["outgoing"])}'),
             ("out_after", f'chainD (fun x => x) {lst(b["outcomes"])}'),
             ("rcpt_after", f'chainD (fun x => x) {lst(b["outgoing"])}'),
             ("empty", "bdigest []"), ("tag0", "bdigest [0]"), ("tag1", "bdigest [1]"), ("tag2", "bdigest [2]")]
    L = ["import NearSpecV3.E2E.ViewE", "open NearSpecV3.E2E.Bnd", "",
         "def hexOf (b : List UInt8) : String :=",
         "  let d := \"0123456789abcdef\".toList",
         "  String.join (b.map fun x => String.ofList [d[(x.toNat / 16)]!, d[(x.toNat % 16)]!])",
         "def nib (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87",
         "def unhex : List Char → List UInt8",
         "  | a :: b :: r => (nib a * 16 + nib b).toUInt8 :: unhex r",
         "  | _ => []",
         "def h (s : String) : List UInt8 := unhex s.toList", "",
         "def main : IO Unit := do"]
    for n, e in exprs:
        L.append(f'  IO.println s!"{n} {{hexOf ({e})}}"')
    return "\n".join(L) + "\n", [n for n, _ in exprs]


def lean_consts(inp, cb, wb, workdir, pkg=bndrec.LEAN_PKG):
    import subprocess
    src, names = lean_consts_source(inp, cb, wb)
    p = os.path.join(workdir, "ViewConsts.lean")
    open(p, "w").write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", "--run", p], cwd=pkg, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=1800)
    except (OSError, subprocess.TimeoutExpired) as x:
        return {"ok": None, "error": str(x)}
    got = {}
    for ln in r.stdout.decode(errors="replace").splitlines():
        sp = ln.split()
        if len(sp) == 2 and sp[0] in names:
            got[sp[0]] = sp[1]
    a, b = inp["acc"]["before"], inp["acc"]["after"]
    want = {"ctx_raw_be": inp["ctx_raw_be"], "u32_lB": inp["lB"].to_bytes(4, "big").hex(),
            "out_before": a["outcomesChain"], "rcpt_before": a["outgoingChain"],
            "out_after": b["outcomesChain"], "rcpt_after": b["outgoingChain"],
            "empty": E.hex(), "tag0": tagd(0).hex(), "tag1": tagd(1).hex(), "tag2": tagd(2).hex()}
    rows = {n: {"lean": got.get(n), "python": want[n], "equal": got.get(n) == want[n]} for n in names}
    return {"ok": r.returncode == 0 and all(x["equal"] for x in rows.values()), "rows": rows, "source": p,
            "error": None if r.returncode == 0 else r.stdout.decode(errors="replace")[-600:]}


# ---------------------------------------------------------------------------
# saved leaves vs the chain
# ---------------------------------------------------------------------------
SAVED = {
    "INIT": f"{DEPS}/e2e-m5d/g5/tmpl/init",
    "IF": f"{DEPS}/laneB-t1/t1b/T1S/if/out",
    "STATE": f"{DEPS}/laneB-t1/t1b/T1S/seg0/out",
    "RT enter": f"{DEPS}/e2e-m5t1/f3/enter-proof",
    "PREP": f"{DEPS}/e2e-laneA/at4/prep/leaf",
    "WASM": f"{DEPS}/e2e-laneA/at2/leaf-k13p/leaf",
    "RT resume": f"{DEPS}/e2e-m5t1/f4/resume-proof",
    "FINAL": f"{DEPS}/e2e-m5d/g5/tmpl/final",
}
TREE = f"{DEPS}/tmp-laneD/m9b"   # lane D's M9 prototype tree (the leaves it imported: imported.sha256)


def _fdiff(a, b, pre=""):
    out = []
    for n, k in bndrec.BND_FIELDS if not pre else bndrec.WASM_FIELDS:
        if n == "wasm":
            if (a["wasm"] is None) != (b["wasm"] is None):
                out.append("wasm")
            elif a["wasm"] is not None:
                out += _fdiff(a["wasm"], b["wasm"], "wasm.")
        elif a[n] != b[n]:
            out.append(pre + n)
    return out


def _rec_row(leaf, path, rec_in, rec_out, c_in, c_out, owner, why):
    d_in, d_out = bndrec.digest(rec_in).hex(), bndrec.digest(rec_out).hex()
    din, dout = _fdiff(rec_in, c_in), _fdiff(rec_out, c_out)
    return {"leaf": leaf, "path": path, "exposes": "full BndRec in / out (public values = BndRec.encode bytes)",
            "d_in": d_in, "d_out": d_out, "plan_d_in": bndrec.digest(c_in).hex(), "plan_d_out": bndrec.digest(c_out).hex(),
            "in_equal": d_in == bndrec.digest(c_in).hex(), "out_equal": d_out == bndrec.digest(c_out).hex(),
            "diff_in": din, "diff_out": dout, "owner": owner, "why": why}


def leaf_table(c, inp, saved=SAVED):
    rows = []
    ex = os.path.exists
    # INIT (G-5): claimDigest (leaf ctx), ctxRoot of B_0 (u32 big-endian), prev_state_root (join value with IF)
    p = saved["INIT"]
    if ex(p):
        pv = json.load(open(f"{p}/INFO.json"))["public_values"][4]
        ctx = limbs3(pv[14:28])
        b0 = dict(c[0], ctxRoot=ctx)     # lane D's wrapper: the view's init constants + the leaf's ctxRoot
        rows.append({"leaf": "INIT (G-5)", "path": p, "exposes": "claimDigest (leaf ctx), ctxRoot(B_0), prev_state_root (PSR)",
                     "checks": {"claimDigest = bdigest(S) (leaf ctx, not a BndRec field)": limbs3(pv[0:14]).hex() == inp.get("claimDigest_S"),
                                "ctxRoot = plan B_0.ctxRoot (ViewE, u32 big-endian)": ctx.hex() == c[0]["ctxRoot"].hex(),
                                "h(B_0) assembled from the leaf = h(c0)": bndrec.digest(b0) == bndrec.digest(c[0]),
                                "prev_state_root = IF's": root16(pv[28:44]).hex() == inp["prev_state_root"]},
                     "in_equal": bndrec.digest(b0) == bndrec.digest(c[0]), "out_equal": False,
                     "owner": "B: B_1 (ctxD (.intake I), R_0) is INTAKE's (the joined INIT + IF leaf); INIT exposes B_0 only",
                     "why": "INIT's B_0 = the chain's c0 (stD .none at the placeholder); B_1 = eng I start is lane B's half"})
    # IF (B-T1b): R_0, R_n, prev / post roots, wsLen, change count
    p = saved["IF"]
    if ex(p):
        s = json.load(open(f"{p}/statement.json"))["statement"]
        rows.append({"leaf": "IF (B-T1b, STATE_IF)", "path": p, "exposes": "prev_state_root, wsLen, R_0, R_n (ws roots), post_state_root, #changes",
                     "checks": {"R_0 = c1.stRoot's ws": dig48(s[17:35]).hex() == inp.get("R_0"),
                                "R_n = c7..c9 stRoot's ws": dig48(s[35:53]).hex() == inp.get("R_n"),
                                "post_state_root = header": root16(s[53:69]).hex() == inp["post_state_root"],
                                "wsLen": s[16] == inp["wsLen"], "#changes = 10": s[69] == 10},
                     "in_equal": None, "out_equal": False,
                     "owner": "B: IF exposes ws roots, not stRoot = bdigest(StCommit.ser); the start cut's R_0 commitment (D-a) and IF-FINAL's finalize leaf (D-b) need STC on both IF halves",
                     "why": "the ws parts agree; stRoot (tag, idx, rest) is not opened by IF"})
    # RT enter (F-3)
    p = saved["RT enter"]
    if ex(p):
        pv = json.load(open(f"{p}/statement.json"))["public_values"]
        rows.append(_rec_row("RT enter (F-3)", p, bndrec.decode(bytes(pv[:450])), bndrec.decode(bytes(pv[450:1284])), c[2], c[3],
                             "F: re-prove enter with the M12 / M11i record (claimDigest = bdigest [], outD (.eng) accumulators + tag, vmAcc = bdigest []); stRoot / ctxRoot wait for B / E",
                             "pre-M12 record: real claimDigest, 0^42 accumulators / tag / vmAcc / proposalsAcc, run4's stRoot placeholder"))
    # PREP (A-T4)
    p = saved["PREP"]
    if ex(p):
        pj = json.load(open(f"{p}/prep.pubs.json"))
        wf = pj["wasm_fields"]
        chk = {"SHA-256(code) ‖ 0^10 = c3.wasm.codeRoot (.pre)": bytes.fromhex(wf["in_code_root"]) == c[3]["wasm"]["codeRoot"],
               "CODE root words = WASM seg 0 (R1)": wf["out_code_root_words"] == inp.get("prep", {}).get("code_root_words"),
               "FUNC root words = WASM seg 0 (R1)": wf["out_func_root_words"] == inp.get("prep", {}).get("func_root_words")}
        rows.append({"leaf": "PREP (A-T4)", "path": p, "exposes": "code hash, |code|; cached CODE / FUNC commitments",
                     "checks": chk, "in_equal": None, "out_equal": None,
                     "owner": "A: PREP's B_in / B_out are not public (`.pre` record from enter, `.ent` = airBnd of the entry); PrepRest; the 42-B root packing; D: insert PREP between enter and WASM 0",
                     "why": "binds the .pre codeRoot cells and the out roots only; the rest of the .ent record is free in lane D's tree"})
    # WASM segments (A-T2)
    p = saved["WASM"]
    if ex(p):
        for k in range(2):
            pj = json.load(open(f"{p}/seg-{k}.pubs.json"))
            b = seg_publics(pj["pubs"], inp["call"]["R"])
            wf = pj["wasm_fields"]
            cr, fr = root42(wf["code_root_words"]), root42(wf["func_root_words"])
            w_in = wasm_air(b["in"], cr, fr, wf["stack_rem_in_unbound"])
            w_out = wasm_air(b["out"], cr, fr, wf["stack_rem_out_unbound"])
            plan_in, plan_out = c[4 + k]["wasm"], c[5 + k]["wasm"]
            d_in, d_out = _fdiff(w_in, plan_in, "wasm."), _fdiff(w_out, plan_out, "wasm.")
            rows.append({"leaf": f"WASM seg {k} (A-T2)", "path": f"{p}/seg-{k}.proof",
                         "exposes": "105 segment publics (pc, sb, clock, gas, ctxDigest, memRoot, depth, nblk) + cached CODE / FUNC",
                         "diff_in": d_in, "diff_out": d_out, "in_equal": not d_in, "out_equal": not d_out,
                         "owner": "A" + (": the halting segment must end at lane A's fin record fbBnd (q, .fin r) (lane F's resume reads it); " if k == 1 else ": ")
                                  + "airBnd must set gasLeft = s.gas.g (M11i); vmCtxDigest / fuel / stackRem not public",
                         "why": "the Wasm part matches the plan where public; the leaf exposes no BndRec (lane D assembles W cells)"
                                + ("; out: the AIR's halted state ≠ the view's `.fin r` record" if k == 1 else "")})
    # RT resume (F-4)
    p = saved["RT resume"]
    if ex(p):
        pv = json.load(open(f"{p}/statement.json"))["public_values"]
        rows.append(_rec_row("RT resume (F-4)", p, bndrec.decode(bytes(pv[247:1081])), bndrec.decode(bytes(pv[1081:1531])), c[6], c[7],
                             "F: re-prove with claimDigest = bdigest [], bwAcc / proposalsAcc = outD (.eng) values, B_in.wasm = lane A's fin record; B: STC answers stRoot (stand-in today)",
                             "F-4 shape (M12 counters, real accumulators) but plan-copied claimDigest / proposalsAcc / bwAcc / ctxRoot, the Wasm part of the run4 plan's last cut, stand-in STC r_out"))
    # STATE (B-T1b): one segment over all 10 changes
    p = saved["STATE"]
    if ex(p):
        s = json.load(open(f"{p}/statement.json"))["statement"]
        rows.append({"leaf": "STATE seg (B-T1b, STATE_SEG)", "path": p, "exposes": "prev_state_root, wsLen, R_in, R_out (ws roots)",
                     "checks": {"R_in = R_0 (c1)": dig48(s[17:35]).hex() == inp.get("R_0"),
                                "R_out = R_n (c7)": dig48(s[35:53]).hex() == inp.get("R_n")},
                     "in_equal": None, "out_equal": False,
                     "owner": "B: split at the RT cuts (seg A: c1 → c2, after 8 changes; seg B: c7 → c8) and expose stRoot via STC (m5tSegC, not re-proved: B-T3); F: STATE engine rows (none)",
                     "why": "one segment R_0 → R_n spans c1 → c9 across the call; no stRoot"})
    # finalize (none)
    rows.append({"leaf": "finalize (STATE, D-b)", "path": None, "exposes": "—", "in_equal": False, "out_equal": False,
                 "owner": "B (IF-FINAL half as a leaf with STC) + F (engine rows yields → done)", "why": "no leaf exists"})
    # FINAL (G-5): B_out = done H o from ctxD (.header H), outD (.done o).1 and the two counters
    p = saved["FINAL"]
    if ex(p):
        pv = json.load(open(f"{p}/INFO.json"))["public_values"][4]
        bo = dict(c[10], ctxRoot=limbs3(pv[30:44]), outcomeAcc=limbs3(pv[44:58]),
                  gasUsed=int.from_bytes(bytes(pv[58:66]), "big"), balanceBurnt=int.from_bytes(bytes(pv[66:82]), "big"))
        rows.append({"leaf": "FINAL (G-5)", "path": p,
                     "exposes": "claimDigest (leaf ctx), finInDigest (join value), n, L, ctxD (.header H), outD (.done o).1, gasUsed, balanceBurnt",
                     "checks": {"claimDigest = bdigest(S)": limbs3(pv[0:14]).hex() == inp.get("claimDigest_S"),
                                "ctxHeaderD = ViewE ctxD (.header H)": bo["ctxRoot"] == c[10]["ctxRoot"],
                                "outDoneD = ViewE outD (.done o).1": bo["outcomeAcc"] == c[10]["outcomeAcc"],
                                "gasUsed / balanceBurnt = done's clear fields": (bo["gasUsed"], bo["balanceBurnt"]) == (c[10]["gasUsed"], c[10]["balanceBurnt"]),
                                "h(B_out) assembled from the leaf = h(c10)": bndrec.digest(bo) == bndrec.digest(c[10])},
                     "in_equal": False, "out_equal": bndrec.digest(bo) == bndrec.digest(c[10]),
                     "owner": "B: B_in = c9 (eng I <done out>) is lane B's FINAL half's (finInDigest is a join value, not a BndRec field)",
                     "why": "FINAL's B_out = the chain's c10 (stD .none at the placeholder); B_in is the other half's"})
    tree = None
    if ex(f"{TREE}/imported.sha256"):
        tree = [ln.split()[1] for ln in open(f"{TREE}/imported.sha256") if ln.strip()]
    return rows, tree


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------
def write_md(out, c, ds, rows, lean, consts, bad, tree):
    L = ["# T1 leaf chain (lane I, I-2, current boundary conventions)", "",
         f"Lean `BndRec.encode`/`bdigest`/`decode` on all {len(c)} cuts: **{lean.get('ok')}**; "
         f"ViewE constants (rawPre, chainD, tags): **{consts.get('ok')}**; convention violations: {len(bad)}.", "",
         "| cut | config | phase | receiptIdx | gasUsed | compute | rPrepaid | digest |", "|---|---|---|---|---|---|---|---|"]
    names = ["init cb wb", "eng I start", "eng I c (receipt 1's step)", "call … .pre", "call … .ent (preConf q)",
             "call … t = 13", "call … .fin r", "eng I c' (after receipt 1)", "eng I ⟨yields _ _ 0⟩", "eng I ⟨done out⟩", "done H o"]
    for i, r in enumerate(c):
        L.append(f"| c{i} | {names[i]} | {r['phase']} | {r['receiptIdx']} | {r['gasUsed']} | {r['compute']} | {r['rPrepaid']} | `{ds[i][:16]}…` |")
    L += ["", "| leaf | lanes | in → out | d_in | d_out |", "|---|---|---|---|---|"]
    for n, lanes, a, b, what in LEAVES:
        L.append(f"| {n} | {lanes} | c{a} → c{b}: {what} | `{ds[a][:12]}` | `{ds[b][:12]}` |")
    L += ["", "## Saved leaves vs the chain", "", "| leaf | exposes | in | out | differs / checks | owner |", "|---|---|---|---|---|---|"]
    for r in rows:
        dif = ", ".join(r.get("diff_in", []) + [x + " (out)" for x in r.get("diff_out", [])]) if "diff_in" in r else \
            "; ".join(f"{k}: {v}" for k, v in r.get("checks", {}).items())
        L.append(f"| {r['leaf']} | {r['exposes']} | {r['in_equal']} | {r['out_equal']} | {dif or '—'} | {r['owner']} |")
    if tree:
        L += ["", "Lane D's M9 prototype tree (`tmp-laneD/m9b`) imported: " + ", ".join(f"`{t}`" for t in tree if t.endswith(".proof"))]
    L += ["", "## Placeholders (0^42 until the owner lands it)", ""] + [f"* {a}: {b} — **{o}**" for a, b, o in PLACEHOLDERS]
    open(os.path.join(out, "chain.md"), "w").write("\n".join(L) + "\n")


def cmd_plan(a):
    inp = json.load(open(a.inputs))
    os.makedirs(a.out, exist_ok=True)
    c = build(inp)
    bad = [x for x in check_conventions(c, inp) if x]
    ds = digests(c)
    lean = consts = {"ok": None}
    if not a.no_lean:
        lean = bndrec.lean_check(c, a.out)
        case = os.path.join(DEPS, "corpora", inp["case"])
        if os.path.exists(os.path.join(case, "claim.bin")):
            consts = lean_consts(inp, open(f"{case}/claim.bin", "rb").read(), open(f"{case}/witness.bin", "rb").read(), a.out)
    rows, tree = leaf_table(c, inp) if not a.no_leaves else ([], None)
    j = {"cuts": [bndrec.to_json(r) for r in c], "digests": ds,
         "leaves": [{"leaf": n, "lanes": l, "in": f"c{x}", "out": f"c{y}", "what": w, "d_in": ds[x], "d_out": ds[y]}
                    for n, l, x, y, w in LEAVES],
         "chain_ok": chain_ok(leaf_pairs(c), ds[0], ds[-1]),
         "conventions_violated": bad, "lean_bndrec": {k: v for k, v in lean.items() if k != "rows"},
         "lean_digests": [x["digest"] for x in lean.get("rows", [])], "lean_consts": consts,
         "saved_leaves": rows, "tree_imports": tree, "placeholders": PLACEHOLDERS}
    json.dump(j, open(os.path.join(a.out, "chain.json"), "w"), indent=1)
    write_md(a.out, c, ds, rows, lean, consts, bad, tree)
    print(open(os.path.join(a.out, "chain.md")).read())
    ok = j["chain_ok"] and not bad and lean["ok"] is not False and consts.get("ok") is not False
    return 0 if ok else 1


def cmd_inputs(a):
    inp = inputs_from_run(a.run, a.lean_run)
    S = os.path.join(a.run, "S.bin")
    if os.path.exists(S):
        inp["claimDigest_S"] = bndrec.bdigest(open(S, "rb").read()).hex()
    wsl = os.path.join(SAVED["WASM"], "seg-0.pubs.json")
    if os.path.exists(wsl):
        wf = json.load(open(wsl))["wasm_fields"]
        inp["prep"] = {"code_root_words": wf["code_root_words"], "func_root_words": wf["func_root_words"]}
    os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
    json.dump(inp, open(a.out, "w"), indent=1)
    print(f"wrote {a.out}")
    return 0


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    p = sp.add_parser("inputs")
    p.add_argument("run")
    p.add_argument("--lean-run", default=LEAN_RUN)
    p.add_argument("--out", default=INPUTS)
    p = sp.add_parser("plan")
    p.add_argument("out")
    p.add_argument("--inputs", default=INPUTS)
    p.add_argument("--no-lean", action="store_true")
    p.add_argument("--no-leaves", action="store_true")
    a = ap.parse_args()
    return {"inputs": cmd_inputs, "plan": cmd_plan}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
