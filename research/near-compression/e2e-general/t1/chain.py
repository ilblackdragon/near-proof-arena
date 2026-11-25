#!/usr/bin/env python3
"""Lane I, I-2 (2026-11-25): T1's leaf chain under the current boundary conventions.

    chain.py inputs RUN_DIR [--lean-run LEAN_RUN.json] [--out data/t1-inputs.json]
    chain.py plan OUT_DIR [--inputs data/t1-inputs.json] [--no-lean] [--no-leaves]
    chain.py rest [--keys STATE_JSON] [--inputs data/t1-inputs.json]     (E2E-M14: Lean evaluation of the cuts' stRoot / ctxRoot)

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
  `bdigest (0 ‖ u32be ℓ_B ‖ u32be |cb| ‖ cb ‖ wb)`, `stRoot = stD .none` (B-T4: lane B's constant `ST_NONE`),
  `outD .none = (bdigest [], [], bdigest [], bdigest [0])`, `vmAcc = bdigest []`.
* M12 `clearE`: `claimDigest = bdigest []`, `blockIdx = actionIdx = t = 0` everywhere; engine cuts
  carry `receiptIdx = |outcomes|`, `gasUsed = gasBurnt = rs.gas`, `balanceBurnt = rs.txBurnt`,
  `compute = rs.compute` (`start`: all 0); a call adds `rPrepaid`; resume outputs `receiptIdx + 1`
  and `rPrepaid = rBurnt = rUsed = 0`; `done H o` carries `o.gasUsed`, `o.balanceBurnt`, the rest 0.
* B-T4 (lane B): `stD .none` is the kernel-evaluated constant `ST_NONE`; `c2 … c6` carry `R_A` (STATE seg
  A's output root); lane B's five leaves (IF at `m5tIFC`, STATE seg A, the resume's state half, seg B,
  the finalize state half, all `m5tSegC`) expose their `STC` row's `r_in` / `r_out`, = the cuts' `stRoot`.
* M13: the `start` cut commits lane B's `R_0` (`EngSt.ovl0`); the finalize step
  (`yields _ _ 0 → done out`) is its own STATE leaf (IF-FINAL); `W` = the whole `stRoot`.
* **M14 (lane E)**: every engine / call cut's record commits to the configuration the next leaf
  computes on. `stRoot` = lane B's `StCommit` under `stViewParams_BI` (lane E's `encRestI`): `tag` =
  the position tag (`StateView.posTag`: `start` 1, `done` 3, `txs` 4, `locals` 5, `delayed` 6,
  `incoming` 7, `yields _ _ 0` 8, other `yields` 9), `rest = bdigest (d_static ‖ d_queue ‖ d_move)`,
  `d_static = bdigest (d_keys ‖ d_shape)`; at `done` (`c9`) there is no overlay: `ws` = the empty
  depth-24 tree's root, `wsLen = 0`, trie `0^32`. `ctxRoot` = `ctxD (.intake I) = bdigest (1 ‖ Ser.enc I)`
  at `c1 … c9`. All of it is Lean-evaluated on T1's run (`join/rest-eval.sh`, `chain.py rest`;
  inputs field `m14`) and cross-checked here (`rest_check`).
* S2 / A-T3: the enter output is lane A's `.pre` record (`fbBnd`: counters 0, digests
  `bdigest []`, `codeRoot = SHA-256(code) ‖ 0^10`); PREP (`.pre → .ent`) follows enter.
* F-4: accumulators are the Lean run's `chainD Ser.enc` (`acc' = bdigest (acc ‖ enc item)`).

Fields no component computes yet are `0^42` placeholders, each listed with its owner in
`PLACEHOLDERS` (M14: `stRoot.rest` and `ctxRoot` are no longer placeholders); a placeholder is the same value at every cut where the view's value is a constant
and changes nowhere else, so the chain holds digest for digest by construction and a
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
# B-T4: `stD .none` of the view's state instance (`stViewParams_B stViewE`): the `stRoot` of `init` /
# `done`, kernel-evaluated (`m5a/lean/join-check/StNoneE.lean`, `stD_none_viewE`; `StNone.stD_none_eq`:
# tag 0, the empty depth-24 tree, wsLen 0, trie `.hash 0^32`, idx 0, rest `bdigest (encRestB (.none))`)
ST_NONE = bytes.fromhex("799a6864c921b6955b6a85356d65c7a612fa488d824fcb1d79623dac5a750e820ff93e8510b26828fe9e")


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


def st_none():
    """`stD .none` recomputed from its record (`StNone.noneCommit`): tag 0, `ws` = the empty depth-24
    tree (`zd nodeH zero48 24`, `nodeH a b = SHA-384 (a ‖ b)`), wsLen 0, trie `0^32`, idx 0,
    rest = `bdigest (lp (encStV .none) ‖ optEnc none) = bdigest 01 00 00`."""
    z = bytes(48)
    for _ in range(24):
        z = hashlib.sha384(z + z).digest()
    return st_commit(0, z, 0, bytes(32), 0, bndrec.bdigest(bytes.fromhex("010000")))


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
    seg_a_root(inp)
    done_digests(inp)
    m14_fixture(inp)
    return inp


def seg_a_root(inp):
    """B-T4: `R_A`, the working-set root after the changes committed before receipt 1 (lane B's STATE
    seg A proof's `R_out`); for T1's claim without the proof, the committed inputs' value."""
    if os.path.exists(LANEB_SEGA):
        inp["R_A"] = dig48(json.load(open(LANEB_SEGA))["statement"][35:53]).hex()
    elif os.path.exists(INPUTS):
        fx = json.load(open(INPUTS))
        if fx.get("claim_sha256") == inp.get("claim_sha256") and fx.get("R_A"):
            inp["R_A"] = fx["R_A"]


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


LANEB_IF = f"{DEPS}/laneB-t1/t4/T1C/if/out/statement.json"      # B-T4 (m5tIFC); B-T1b: t1b/T1S/if/out
LANEB_SEGA = f"{DEPS}/laneB-t1/t4/T1C/seg0/out/statement.json"    # B-T4: STATE seg A (R_A = its R_out)


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
    ("wasm.vmCtxDigest", "bdigest (encRest (.other (q, cc)) / (.air …))", "A (m6 §6; gasLeft is public since A-T5 and blank drops gas.g; needs σ at host rows)"),
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
    `promisesDigest = bdigest []`, **`gasLeft = g`** (M11i; lane A A-T5: `airBnd.gasLeft = s.gas.g`,
    public as `g_out`), `stackRem` (A-T5: public at the out-cut), code / func roots (PREP's cached
    commitments)."""
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


# ---------------------------------------------------------------------------
# E2E-M14 (lane E): the engine cuts' stRoot / ctxRoot, Lean-evaluated (`join/rest-eval.sh`)
# ---------------------------------------------------------------------------
REST_EVAL = os.path.join(HERE, "..", "join", "rest-eval.sh")
M14_CUTS = ("c1", "c2", "c7", "c8", "c9")      # the engine cuts (c3 … c6 carry c2's state component)
POS_TAG = {"start": 1, "done": 3, "txs": 4, "locals": 5, "delayed": 6, "incoming": 7}


def pos_tag(pos):
    """`StateView.posTag` from the evaluator's position name (`yields/yf/yn/fuel/i/k`)."""
    sp = pos.split("/")
    if sp[0] == "yields":
        return 8 if sp[3] == "0" else 9
    return POS_TAG[sp[0]]


def chain_r(items):
    """`View.chainR id`: `[] ↦ bdigest []`, `a :: l ↦ bdigest (chainR l ‖ a)` (the head is outermost)."""
    a = E
    for x in reversed(items):
        a = bndrec.bdigest(a + x)
    return a


def ws_empty():
    """The empty depth-24 working-set tree's root (`zd nodeH zero48 24`; `StNone.wsRoot_nil`)."""
    z = bytes(48)
    for _ in range(24):
        z = hashlib.sha384(z + z).digest()
    return z


def m14_fixture(inp):
    """M14: the committed Lean evaluation (`m14`) for T1's claim, when `inp` lacks it."""
    if not inp.get("m14") and os.path.exists(INPUTS):
        fx = json.load(open(INPUTS))
        if fx.get("claim_sha256") == inp.get("claim_sha256") and fx.get("m14"):
            inp["m14"] = fx["m14"]


def m14_ws(inp):
    """The working-set root of each engine cut: lane B's `R_0` / `R_A` / `R_n`; `c9` (done): the empty tree."""
    return {"c1": inp.get("R_0"), "c2": inp.get("R_A"), "c7": inp.get("R_n"), "c8": inp.get("R_n"),
            "c9": ws_empty().hex()}


def rest_check(inp):
    """M14: the Lean evaluation (`inp["m14"]`) recomputed / cross-checked in Python; the violations."""
    m = inp.get("m14")
    if not m:
        return ["no m14 evaluation"]
    bad = []

    def need(cond, msg):
        if not cond:
            bad.append(msg)
    H = lambda x: bytes.fromhex(x)  # noqa: E731
    cs = m["cuts"]
    ws = m14_ws(inp)
    keys = sorted(bytes.fromhex(k) for k in m["keys"])
    need([bytes.fromhex(k) for k in m["keys"]] == keys and len(keys) == inp["wsLen"], "keys: lane B's leaf order, wsLen")
    need(H(m["empty"]) == E and H(m["ws_empty"]) == ws_empty(), "bdigest [] / the empty tree's root")
    need(len(H(m["ctx_intake"])) == 42 and m["ctx_intake"] != inp["ctx_raw_be"], "ctxD (.intake I) is a 42-B digest")
    for n in M14_CUTS:
        x = cs[n]
        g = {k: H(x[k]) for k in ("d_keys", "d_shape", "d_static", "d_queue", "d_move", "rest", "encRestI", "trie")}
        q = [H(a) for a in x["queue"]]
        need(x["fits"] is True and int(x["idx"]) == 0, f"{n}: circuit form, idx 0")
        need(int(x["tag"]) == pos_tag(x["pos"]), f"{n}: tag = posTag ({x['pos']})")
        need(g["encRestI"] == g["d_static"] + g["d_queue"] + g["d_move"], f"{n}: encRestI = d_static ‖ d_queue ‖ d_move")
        need(g["rest"] == bndrec.bdigest(g["encRestI"]), f"{n}: rest = bdigest (encRestI)")
        need(g["d_static"] == bndrec.bdigest(g["d_keys"] + g["d_shape"]), f"{n}: d_static = bdigest (d_keys ‖ d_shape)")
        need(g["d_queue"] == chain_r(q), f"{n}: d_queue = chainR id (queue items)")
        need(H(x["d_keys"]) == H(cs["c1"]["d_keys"]), f"{n}: d_keys constant")
        if n == "c9":
            need(int(x["wsLen"]) == 0 and g["trie"] == bytes(32) and g["d_shape"] == H(m["d_shape_none"]),
                 "c9 (done): no overlay — wsLen 0, trie 0^32, d_shape = bdigest (Ser.enc none)")
        else:
            need(int(x["wsLen"]) == inp["wsLen"] and g["trie"].hex() == inp["prev_state_root"],
                 f"{n}: wsLen, trie = prev_state_root")
            need(x["keys"] == m["keys"], f"{n}: working-set keys = κ I")
            need(g["d_static"] == H(cs["c1"]["d_static"]), f"{n}: d_static constant before done")
        st = st_commit(int(x["tag"]), H(ws[n]), int(x["wsLen"]), g["trie"], 0, g["rest"]) if ws[n] else None
        need(x.get("ws_root") == ws[n] and st is not None and x.get("stRoot") == st.hex(),
             f"{n}: stRoot (Lean, StCommit.ser) = Python st_commit")
    # the cuts are T1's: the receipt-state counters and committed changes are lane F's dump's
    b, a = inp["acc"]["before"], inp["acc"]["after"]
    for n, side, nout in (("c2", b, len(b["outcomes"])), ("c7", a, len(a["outcomes"])), ("c8", a, len(a["outcomes"]))):
        rs = cs[n]["rs"]
        need((int(rs["gas"]), int(rs["compute"]), int(rs["txBurnt"]), int(rs["nOutcomes"])) ==
             (side["gas"], side["compute"], side["txBurnt"], nout), f"{n}: RS counters = lane F's dump")
        need(dict((k, v) for k, v in cs[n]["written"]) == dict(map(tuple, side["committed"])),
             f"{n}: written entries = the committed changes")
    need(cs["c1"]["pos"] == "start" and cs["c2"]["pos"].startswith("incoming/") and int(cs["c2"]["pos"].split("/")[1]) >= 1,
         "c1 start, c2 incoming with receipt 1 at the head")
    need(cs["c7"]["queue"] == cs["c2"]["queue"][1:], "c7's queue = c2's tail (receipt 1 popped)")
    need(cs["c8"]["pos"].split("/")[0] == "yields" and cs["c8"]["pos"].split("/")[3] == "0" and cs["c9"]["pos"] == "done",
         "c8 = yields _ _ 0, c9 = done")
    rcpt = inp.get("receipt1_ser")
    need(rcpt is None or cs["c2"]["queue"][:1] == [rcpt], "c2's queue head = lane F's dump's receipt (Ser.enc)")
    return bad


def m14_eval(inp, case, workdir, pkg=None):
    """Run the Lean evaluator (`join/rest-eval.sh`) on T1's case with the inputs' key list and lane B's
    working-set roots; returns its JSON (with `keys`)."""
    import subprocess
    keys = inp.get("m14", {}).get("keys") or inp.get("keys")
    ws = {k: v for k, v in m14_ws(inp).items() if k != "c9" and v}
    src = os.path.join(workdir, "rest-in.json")
    out = os.path.join(workdir, "rest-out.json")
    json.dump({"keys": keys, "ws": ws}, open(src, "w"))
    env = dict(os.environ, TMPDIR=workdir)
    if pkg:
        env["M5A_PKG"] = pkg
    r = subprocess.run(["bash", REST_EVAL, case, src, out], stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                       env=env, timeout=1800)
    if r.returncode != 0 or not os.path.exists(out):
        raise RuntimeError(r.stdout.decode(errors="replace")[-2000:])
    j = json.load(open(out))
    j["keys"] = keys
    return j


# the leaves: (name, lanes, cut in, cut out, what)
LEAVES = [
    ("INIT ⊕ IF", "G (INIT) ⊕ B (IF-INTAKE)", 0, 1, "init cb wb → eng I start (split leaf: CLM bytes + PSR join)"),
    ("STATE seg A", "B ⊕ F (engine rows)", 1, 2, "VM-free steps up to receipt 1's step (receipt 0, the 3 forwards)"),
    ("RT enter", "F", 2, 3, "eng I c → call I c [] q .pre"),
    ("PREP", "A", 3, 4, ".pre → .ent (cstep q .pre = preConf q)"),
    ("WASM seg 0", "A", 4, 5, "steps (0, 13]"),
    ("WASM seg 1", "A", 5, 6, "steps (13, 26], halts → .fin r"),
    ("RT resume", "F ⊕ B (STC)", 6, 7, "estepO (strictO [(q, r)]): refund, outcome, outgoing receipt"),
    ("STATE seg B", "B ⊕ F (engine rows)", 7, 8, "VM-free steps after receipt 1 → eng I ⟨yields _ _ 0⟩ (T1: 2 steps, incoming [] → yields → yields _ _ 0)"),
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
    st_none = ST_NONE
    # B-T4: the working-set root after the 8 changes committed before receipt 1 (lane B's STATE seg A
    # output, `R_A`); c2 … c6 carry it
    ra = bytes.fromhex(inp["R_A"]) if inp.get("R_A") else bytes(48)
    code_root, func_root = bytes(42), bytes(42)
    if inp.get("prep"):
        code_root, func_root = root42(inp["prep"]["code_root_words"]), root42(inp["prep"]["func_root_words"])

    m14 = inp.get("m14")

    def st(cut, ws):
        """M14: the cut's `StCommit` (Lean-evaluated tag / rest; c9 = done: empty tree, wsLen 0, trie 0^32)."""
        if not m14:          # pre-M14 placeholders (tag 1 / 3, rest 0^42)
            return st_commit(3 if cut == "c9" else 1, ws, wslen, prev, 0, ZERO)
        x = m14["cuts"][cut]
        if cut == "c9":
            return st_commit(int(x["tag"]), ws_empty(), 0, bytes(32), 0, bytes.fromhex(x["rest"]))
        return st_commit(int(x["tag"]), ws, wslen, prev, 0, bytes.fromhex(x["rest"]))

    ctx_i = bytes.fromhex(m14["ctx_intake"]) if m14 else ZERO     # ctxD (.intake I) at c1 … c9
    eng0 = dict(outcomeAcc=E, outRcptAcc=[E], proposalsAcc=E, bwAcc=tagd(1))
    c = [None] * 11
    c[0] = _rec("init", ctxRoot=bytes.fromhex(inp["ctx_raw_be"]), stRoot=st_none,
                outcomeAcc=E, outRcptAcc=[], proposalsAcc=E, bwAcc=tagd(0))
    c[1] = _rec("eng", ctxRoot=ctx_i, stRoot=st("c1", r0), **eng0)
    c[2] = _rec("eng", ctxRoot=ctx_i, stRoot=st("c2", ra), **_eng_acc(acc_b),
                **_eng_clear(acc_b, len(acc_b["outcomes"])))
    c[3] = dict(c[2], phase=bndrec.PHASE["call"], inCall=True, rPrepaid=call["prepaid"],
                wasm=wasm_pre(call["code_sha256"]))
    c[4] = dict(c[3], wasm=wasm_air(segs[0]["in"], code_root, func_root, call["stackRem"]))
    c[5] = dict(c[3], wasm=wasm_air(segs[0]["out"], code_root, func_root, call["stackRem"]))
    c[6] = dict(c[3], wasm=wasm_fin())
    c[7] = _rec("eng", ctxRoot=ctx_i, stRoot=st("c7", rn), **_eng_acc(acc_a),
                **_eng_clear(acc_a, len(acc_a["outcomes"])))
    c[8] = dict(c[7], stRoot=st("c8", rn))
    c[9] = dict(c[7], stRoot=st("c9", rn), receiptIdx=inp["n_outcomes"], gasUsed=inp["gasUsed"],
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
T4 = f"{DEPS}/laneB-t1/t4/T1C"   # B-T4: lane B's leaves cut at the rt boundaries (m5a/leaf.sh --ifc --seg-keys)
SAVED = {
    "INIT": f"{DEPS}/e2e-m5d/g5/tmpl/init",
    "IF": f"{T4}/if/out",
    "STATE": f"{T4}/seg0/out",
    "RT enter": f"{DEPS}/e2e-m5t1/f7/enter-proof",       # F-7: c2 -> c3 on the M14 chain (F-6 AIR)
    "PREP": f"{DEPS}/e2e-laneA/at4/prep/leaf",
    "WASM": f"{DEPS}/e2e-laneA/at5/leaf-k13/leaf",
    "RT resume": f"{DEPS}/e2e-m5t1/f7/resume-proof",     # F-7: c6 -> c7 on the M14 chain (STC metas = m14)
    "FINAL": f"{DEPS}/e2e-m5d/g5/tmpl/final",
}
# B-T4: the other three state halves (out/ = proof + statement + htape.json, the STC stand-in's messages)
SAVED_B = {"STATE R": f"{T4}/seg1/out", "STATE B": f"{T4}/seg2/out", "STATE fin": f"{T4}/seg3/out"}
# F-5: lane F's STATE engine halves (`SE`, proof + statement: the two records' BndRec.encode bytes);
# F-6: re-proved with every public value byte-checked in-circuit (`Ids.pubBytes`)
# F-7: the M14 chain, with the opening rows (`SH`: stRoot / encRestI open and close)
SAVED_F = {"STATE seg A": f"{DEPS}/e2e-m5t1/f7/se-seg-a-proof", "STATE seg B": f"{DEPS}/e2e-m5t1/f7/se-seg-b-proof",
           "finalize": f"{DEPS}/e2e-m5t1/f7/se-finalize-proof"}
TREE = f"{DEPS}/tmp-laneD/m9b"   # lane D's M9 prototype tree (the leaves it imported: imported.sha256)


# E2E-M14: the leaves whose exposed records / STC messages carry c1 … c9's stRoot or ctxRoot; each must be
# re-proved on the M14 chain (until then its row differs exactly in those fields: `test_chain_saved_leaves`)
M14_REPROVE = {
    "IF (B-T4, m5tIFC)": "B: STC r_in = c1 (tag 1, encRestI rest), r_out = c9 (tag 3, done: empty ws, wsLen 0, trie 0^32)",
    "STATE seg A (B-T4)": "B: STC c1 → c2 (tags 1 → 7, rests)",
    "RT resume, state half (B-T4)": "B: STC c6 → c7 (tags 7 → 7, rests)",
    "STATE seg B (B-T4)": "B: STC c7 → c8 (tags 7 → 8, rests)",
    "finalize, state half (B-T4)": "B: STC c8 → c9 (tags 8 → 3; the done close: empty ws, wsLen 0, trie 0^32)",
    "RT enter (F-7)": "F: records c2 → c3 (stRoot, ctxRoot)",
    "RT resume (F-7)": "F: records c6 → c7 (stRoot, ctxRoot)",
    "STATE seg A, engine half (F-7 SE)": "F: records c1 → c2",
    "STATE seg B, engine half (F-7 SE)": "F: records c7 → c8",
    "finalize, engine half (F-7 SE)": "F: records c8 → c9",
}
M14_FIELDS = {"stRoot", "ctxRoot"}
M14_STC = {"r_in", "r_out", "tags (in, out)"}


def m14_stale(row):
    """A saved leaf that differs from the M14 chain only in the fields M14 moved (re-prove pending)."""
    if row["leaf"] not in M14_REPROVE or (row.get("in_equal") and row.get("out_equal")):
        return False
    if "diff_in" in row:
        return set(row["diff_in"]) | set(row["diff_out"]) <= M14_FIELDS
    return all(v for k, v in row["checks"].items() if not any(k.startswith(x) for x in M14_STC))


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


def full_pv(path):
    """F-6 (lane D's F-M9-1): the leaf's statement carries its whole public-value vector in one AIR (the
    boundary table reads every value: lane F's `Ids.pubBytes` byte lookups), so the records the tree
    hashes are in the proof; and every value is a byte."""
    if path is None or not os.path.exists(os.path.join(path, "statement.json")):
        return False
    st = json.load(open(os.path.join(path, "statement.json")))
    pv = st["public_values"]
    return any(a["num_public_values"] == len(pv) for a in st["airs"]) and all(0 <= v < 256 for v in pv)


def _rec_row(leaf, path, rec_in, rec_out, c_in, c_out, owner, why):
    d_in, d_out = bndrec.digest(rec_in).hex(), bndrec.digest(rec_out).hex()
    din, dout = _fdiff(rec_in, c_in), _fdiff(rec_out, c_out)
    return {"leaf": leaf, "path": path, "exposes": "full BndRec in / out (public values = BndRec.encode bytes)",
            "d_in": d_in, "d_out": d_out, "plan_d_in": bndrec.digest(c_in).hex(), "plan_d_out": bndrec.digest(c_out).hex(),
            "in_equal": d_in == bndrec.digest(c_in).hex(), "out_equal": d_out == bndrec.digest(c_out).hex(),
            "diff_in": din, "diff_out": dout, "owner": owner, "why": why,
            "checks": {"public values: full records in one AIR, bytes (F-6)": full_pv(path)}}


def stc_msgs(out_dir):
    """The `STC` row's messages of a lane B leaf (the stand-in for lane F's engine rows, `htape.json`
    of the dump): `STMQ` (211) `[r_in, tag_out, rest_out]`, `STMA` (212) `[r_out, tag_in, rest_in]`
    (digests as 14 three-byte big-endian limbs)."""
    f = os.path.join(out_dir, "htape.json")
    if not os.path.exists(f):
        f = os.path.join(os.path.dirname(out_dir.rstrip("/")), "htape.json")
    ht = json.load(open(f))
    q = next(m for b, snd, m in ht if b == 211)
    a = next(m for b, snd, m in ht if b == 212)
    return {"r_in": limbs3(q[:14]), "tag_out": q[14], "rest_out": limbs3(q[15:29]),
            "r_out": limbs3(a[:14]), "tag_in": a[14], "rest_in": limbs3(a[15:29])}


def _state_row(leaf, path, c, a, b, inp, ws_in, ws_out, tags, owner, why):
    """A lane B state half (`m5tSegC` / `m5tIFC`): the `STC` row's `r_in` / `r_out` against the cuts'
    `stRoot`, the records assembled with them (the other fields: lane F's engine half / lane D's
    wrapper), the public working-set roots, `wsLen`, the trie and the stand-in's tags."""
    st = json.load(open(f"{path}/statement.json"))["statement"]
    m = stc_msgs(path)
    rin, rout = dict(c[a], stRoot=m["r_in"]), dict(c[b], stRoot=m["r_out"])
    chk = {f"r_in = c{a}.stRoot": m["r_in"] == c[a]["stRoot"], f"r_out = c{b}.stRoot": m["r_out"] == c[b]["stRoot"],
           "R_in (values 17-34)": dig48(st[17:35]).hex() == ws_in, "R_out (values 35-52)": dig48(st[35:53]).hex() == ws_out,
           "wsLen": st[16] == inp["wsLen"],
           "prev_state_root (= the opened trie, Stc.trieEqs)": root16(st[0:16]).hex() == inp["prev_state_root"],
           "tags (in, out)": (m["tag_in"], m["tag_out"]) == tags}
    d_in, d_out = bndrec.digest(rin).hex(), bndrec.digest(rout).hex()
    return {"leaf": leaf, "path": path, "exposes": "STC: r_in / r_out (STMQ / STMA), R_in, R_out, wsLen, prev_state_root",
            "checks": chk, "d_in": d_in, "d_out": d_out,
            "in_equal": d_in == bndrec.digest(c[a]).hex(), "out_equal": d_out == bndrec.digest(c[b]).hex(),
            "owner": owner, "why": why}, st


def _tags(inp, a, b):
    """The STC (tag_in, tag_out) of a lane B half: the cuts' M14 tags (pre-M14: 1 / 3)."""
    m = inp.get("m14")
    if not m:
        return (1, 3 if b == "c9" else 1)
    return (int(m["cuts"][a]["tag"]), int(m["cuts"][b]["tag"]))


def leaf_table(c, inp, saved=SAVED, saved_b=SAVED_B):
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
                     "owner": "B-T4: B_1's stRoot is the IF's STC r_in (c1); G: B_1's ctxRoot = ctxD (.intake I) in-circuit (M14: the value is on the chain, Lean-evaluated; preimage 1 ‖ Ser.enc I); D: the joined INIT + IF leaf; INIT exposes B_0 only",
                     "why": "INIT's B_0 = the chain's c0 (lane G's wrapper takes stD .none: B-T4's constant); B_1 = eng I start: its stRoot is the IF's STC r_in (B-T4), its ctxRoot ctxD (.intake I) (M14)"})
    # IF (B-T4, m5tIFC): the INTAKE half closes c1's stRoot (R_0, tag 1), the FINAL half opens c9's (R_n, tag 3)
    p = saved["IF"]
    if ex(p):
        row, st = _state_row("IF (B-T4, m5tIFC)", p, c, 1, 9, inp, inp.get("R_0"), inp.get("R_n"), _tags(inp, "c1", "c9"),
                             "G / D: c1's ctxRoot (ctxD (.intake I)) from the joined INIT leaf; F: the engine rows that open / close rest (encRestI, M14)",
                             "the INTAKE half's stRoot (InitBOut's state part) is c1's and the FINAL half's (FinPre's) is c9's")
        row["checks"].update({"post_state_root = header": root16(st[53:69]).hex() == inp["post_state_root"],
                              "#changes = 10": st[69] == 10})
        row["exposes"] = "STC (c1 / c9 stRoot), prev_state_root, wsLen, R_0, R_n, post_state_root, #changes"
        rows.append(row)
    # RT enter (F-3)
    p = saved["RT enter"]
    if ex(p):
        pv = json.load(open(f"{p}/statement.json"))["public_values"]
        rows.append(_rec_row("RT enter (F-7)", p, bndrec.decode(bytes(pv[:450])), bndrec.decode(bytes(pv[450:1284])), c[2], c[3],
                             "F: EntChecks.prepaid / .code (join with the receipt rows); A: vmCtxDigest (placeholder shared with the chain)",
                             "F-6: proved from this chain's c2 -> c3 (rtbnd.pair_chain), every public value byte-checked in-circuit; re-prove when the chain moves"))
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
    # WASM segments (A-T5: stackRem / gasLeft public, the halting segment emits the fin record)
    p = saved["WASM"]
    if ex(p):
        for k in range(2):
            pj = json.load(open(f"{p}/seg-{k}.pubs.json"))
            b = seg_publics(pj["pubs"], inp["call"]["R"])
            wf = pj["wasm_fields"]
            cr, fr = root42(wf["code_root_words"]), root42(wf["func_root_words"])
            at5 = "gas_left_out" in wf
            # the in-record's stackRem / gasLeft are the previous leaf's out (bound there); the
            # out-record's are the leaf's publics (A-T5), or the fin record for a halting segment
            w_in = wasm_air(b["in"], cr, fr, wf["stack_rem_in_unbound"])
            if wf.get("out_record") == "fin":
                w_out = wasm_fin()
            else:
                w_out = wasm_air(b["out"], cr, fr, wf["stack_rem_out"] if at5 else wf["stack_rem_out_unbound"])
                if at5:
                    w_out["gasLeft"] = wf["gas_left_out"]
            plan_in, plan_out = c[4 + k]["wasm"], c[5 + k]["wasm"]
            d_in, d_out = _fdiff(w_in, plan_in, "wasm."), _fdiff(w_out, plan_out, "wasm.")
            dg_in = bndrec.digest(dict(c[4 + k], wasm=w_in)).hex()
            dg_out = bndrec.digest(dict(c[5 + k], wasm=w_out)).hex()
            rows.append({"leaf": f"WASM seg {k} ({'A-T5' if at5 else 'A-T2'})", "path": f"{p}/seg-{k}.proof",
                         "exposes": "117 segment publics (pc, sb, clock, gas register, ctxDigest, memRoot, depth, nblk; A-T5: "
                                    "stackRem halves, g_out limbs, R bytes) + cached CODE / FUNC"
                                    + ("; out-record = the fin record" if wf.get("out_record") == "fin" else ""),
                         "diff_in": d_in, "diff_out": d_out, "in_equal": not d_in, "out_equal": not d_out,
                         "d_in": dg_in, "d_out": dg_out,
                         "d_in_equal": dg_in == bndrec.digest(c[4 + k]).hex(), "d_out_equal": dg_out == bndrec.digest(c[5 + k]).hex(),
                         "owner": "A: vmCtxDigest, fuel not public (placeholders shared with the chain); the 42-B packing of the "
                                  "cached CODE / FUNC commitment",
                         "why": "the Wasm part matches the plan field by field; the leaf exposes no BndRec (lane D assembles W cells)"})
    # RT resume (F-4)
    p = saved["RT resume"]
    if ex(p):
        pv = json.load(open(f"{p}/statement.json"))["public_values"]
        rows.append(_rec_row("RT resume (F-7)", p, bndrec.decode(bytes(pv[247:1081])), bndrec.decode(bytes(pv[1081:1531])), c[6], c[7],
                             "F: RsStep (estepO composition), in-circuit Ser.enc items; A: RsFin (vmCtxDigest opening); B/D: one trace with B-T4's state half (XTAPE stand-in = its htape)",
                             "F-5: proved from this chain's c6 -> c7; B_in.wasm = lane A's fin record, checked in-circuit (finInCons)"))
    # STATE (B-T4): the segment cut at the rt boundaries, m5tSegC
    p = saved["STATE"]
    if ex(p):
        rows.append(_state_row("STATE seg A (B-T4)", p, c, 1, 2, inp, inp.get("R_0"), inp.get("R_A"), _tags(inp, "c1", "c2"),
                               "F: STATE engine rows (receipt 0's three forwards: counters, outcome / outgoing appends)",
                               "the 8 changes before receipt 1; stRoot in / out = c1 / c2")[0])
    p = saved_b["STATE R"]
    if ex(p):
        rows.append(_state_row("RT resume, state half (B-T4)", p, c, 6, 7, inp, inp.get("R_A"), inp.get("R_n"), _tags(inp, "c2", "c7"),
                               "F: join with the resume leaf (its RB rows send STMQ / take STMA in STC's layout; XTAPE stand-in today)",
                               "receipt 1's 2 changes; stRoot in / out = c6 / c7")[0])
    p = saved_b["STATE B"]
    if ex(p):
        rows.append(_state_row("STATE seg B (B-T4)", p, c, 7, 8, inp, inp.get("R_n"), inp.get("R_n"), _tags(inp, "c7", "c8"),
                               "F: STATE engine rows (two VM-free steps on T1: incoming [] → yields → yields _ _ 0)",
                               "no working-set change; M14: c7 ≠ c8 (tag 7 → 8, rest)")[0])
    p = saved_b["STATE fin"]
    if ex(p):
        rows.append(_state_row("finalize, state half (B-T4)", p, c, 8, 9, inp, inp.get("R_n"), inp.get("R_n"), _tags(inp, "c8", "c9"),
                               "F: finalize engine rows (yields → done: counters, rest); the IF's FINAL half closes the same c9 stRoot (join value)",
                               "opens c8's stRoot, closes c9's (tag 3); FinHalfB's batched FINAL is the IF proof's")[0])
    else:
        rows.append({"leaf": "finalize (STATE, D-b)", "path": None, "exposes": "—", "in_equal": False, "out_equal": False,
                     "owner": "B (IF-FINAL half as a leaf with STC) + F (engine rows yields → done)", "why": "no leaf exists"})
    # STATE engine halves (F-5): SE leaves, full BndRec in / out
    for nm, (a_, b_) in (("STATE seg A", (1, 2)), ("STATE seg B", (7, 8)), ("finalize", (8, 9))):
        p = SAVED_F[nm]
        if ex(f"{p}/statement.json"):
            pv = json.load(open(f"{p}/statement.json"))["public_values"]
            rows.append(_rec_row(f"{nm}, engine half (F-7 SE)", p, bndrec.decode(bytes(pv[:450])), bndrec.decode(bytes(pv[450:900])),
                                 c[a_], c[b_], "F-7: opening rows (SH: stRoot / encRestI open + close) in the proof; SeStep (working-set) = circuit + SeMove; F: SeMove (the VM-free step semantics on the opened bytes); "
                                 "B/D: one trace with B-T4's state half (XTAPE stand-in = its htape)",
                                 "SE: boundary rules + STMQ/STMA; proved from this chain's records"))
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
                     "owner": "B-T4: c9's stRoot = the IF's STC r_out (FinPre's state part); D: B_in = c9 in the joined FINAL leaf (finInDigest is a join value, not a BndRec field)",
                     "why": "FINAL's B_out = the chain's c10 (stD .none: B-T4's constant); B_in = c9, whose stRoot is the IF's STC r_out (B-T4)"})
    for r in rows:
        r["m14_stale"] = m14_stale(r)
        if r["m14_stale"]:
            r["owner"] = "re-prove (E2E-M14): " + M14_REPROVE[r["leaf"]] + "; " + r["owner"]
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
    stale = [r["leaf"] for r in rows if r.get("m14_stale")]
    if stale:
        L += ["", "**E2E-M14: re-prove on this chain** (each differs only in the moved `stRoot` / `ctxRoot` / `STC` "
              "tags and rests): " + ", ".join(stale)]
    L += ["", "## Placeholders (0^42 until the owner lands it)", ""] + [f"* {a}: {b} — **{o}**" for a, b, o in PLACEHOLDERS]
    open(os.path.join(out, "chain.md"), "w").write("\n".join(L) + "\n")


def cmd_plan(a):
    inp = json.load(open(a.inputs))
    os.makedirs(a.out, exist_ok=True)
    c = build(inp)
    bad = [x for x in check_conventions(c, inp) if x] + (rest_check(inp) if inp.get("m14") else [])
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


def cmd_rest(a):
    """M14: run the Lean evaluator on T1 and store its output as the inputs' `m14` field."""
    inp = json.load(open(a.inputs))
    if a.keys:
        st = json.load(open(a.keys))
        inp["keys"] = sorted(set(st["keys_read"]) | set(k for k, _ in st["changes"]), key=bytes.fromhex)
    case = os.path.join(DEPS, "corpora", inp["case"])
    os.makedirs(a.work, exist_ok=True)
    m = m14_eval(inp, case, a.work, a.pkg)
    inp.pop("keys", None)
    inp["m14"] = m
    if os.path.exists(LEAN_RUN):
        inp["receipt1_ser"] = json.load(open(LEAN_RUN))["receipts"][0]["receipt"]["ser"]
    bad = rest_check(inp)
    print("\n".join(bad) if bad else "rest_check: ok")
    json.dump(inp, open(a.out or a.inputs, "w"), indent=1)
    return 1 if bad else 0


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
    p = sp.add_parser("rest")
    p.add_argument("--inputs", default=INPUTS)
    p.add_argument("--keys", help="a state.json (keys_read, changes): the key list κ I in leaf order")
    p.add_argument("--work", default=os.path.join(DEPS, "tmp-laneE", "m14"))
    p.add_argument("--pkg", help="lane B's package (default: ../m5a/lean)")
    p.add_argument("--out")
    a = ap.parse_args()
    return {"inputs": cmd_inputs, "plan": cmd_plan, "rest": cmd_rest}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
