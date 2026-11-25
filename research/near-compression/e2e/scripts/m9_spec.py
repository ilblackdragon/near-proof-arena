#!/usr/bin/env python3
"""E2E-D M9: the heterogeneous-tree spec over REAL T1 leaves only (no stub template).

    m9_spec.py WORK ARITY DEPTH      reads WORK/tmpl/<leaf>/INFO.json (m9_import.sh)

Leaves (lane I's T1 plan, Templates.lean's honest chain):
  INIT (lane G G-3) | STATE_IF (lane B B-T1) | RT_ENTER (lane F F-2) | WASM seg 0, 1 (lane A A-T1) |
  RT_RESUME (lane F F-2) | STATE_SEG (lane B B-T1) | FINAL (lane G G-3)

Boundary record: named regions (REGIONS below). Every leaf writes the regions its child exposes and
passes the others through unchanged. A region no real leaf produces before its consumer is
introduced at INIT as private witness cells ("free"); a region no real leaf consumes is read by
FINAL into private witness cells ("dropped"). The `edges` table in the spec JSON (and the printout)
lists, per edge, which record cells are bound on both sides, carried, free or dropped.

Bindings across leaves (both sides are public values / commitments of real leaves):
  * INIT pv 28..44 (main slot prev_state_root, pack2) = STATE_IF WSB/WSX pv 0..15   [PSR join]
  * lane B chain: STATE_IF (prev, wsLen, R_0) -> STATE_SEG (prev, wsLen, R_in), and FINAL's leaf reads
    the last R_out and IF's R_n from one witness cell (R_out(last seg) = R_n, as M8)
  * WASM seg 0 -> seg 1: lane A's boundary fields + CODE / FUNC roots (as M8)
  * RT_ENTER B_out -> RT_RESUME B_in: lane E BndRec.encode bytes 0..408 of the call record, all but
    `t` (400 bytes: claimDigest, phase, indices, inCall, stRoot, ctxRoot, gas / compute / balance,
    rPrepaid, rBurnt, rUsed, accumulators, vmAcc, wasm tag), carried unchanged across the WASM leaves
  * ctx = claimDigest: INIT and FINAL bind it from their pv 0..14 (CtxMode::Src)
FINAL's B_out digests (pv 28..58: n, L, ctxD(.header H), outD(.done o).1) have no record (the
tree's DONE state is fixed): pinned as constants of the FINAL leaf program (T1's values).
"""
import hashlib, json, os, sys
from pathlib import Path

W, ARITY, DEPTH = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
T = W / "tmpl"
I = {d.name: json.load(open(d / "INFO.json")) for d in T.iterdir() if (d / "INFO.json").exists()}
wasm_names = sorted(n for n in I if n.startswith("wasm"))
assert len(wasm_names) >= 1

def pv_group(info):
    g = [a for a, v in enumerate(info["public_values"]) if v]
    g.sort(key=lambda a: -len(info["public_values"][a]))
    v0 = info["public_values"][g[0]]
    for a in g:
        assert info["public_values"][a] == v0[:len(info["public_values"][a])], "public values not a prefix"
    return g

P = lambda a, lo, n: [["pv", a, lo + j] for j in range(n)]
C = lambda k: [["cached", k, l] for l in range(18)]
Z = lambda n: [["const", 0]] * n

# ---------------- lane A (m8_spec.py layout)
PC_IN, PC_OUT, CTX_IN, CTX_OUT, MEM_IN, MEM_OUT = 11, 21, 31, 49, 67, 85
STATUS, MEMSZ, DEPTH_P, NBLK = 8, 9, 103, 104
ia = I[wasm_names[0]]
ga = pv_group(ia); a0 = ga[0]
assert len(ia["public_values"][a0]) == 105
w_in = P(a0, PC_IN, 9) + P(a0, CTX_IN, 18) + P(a0, MEM_IN, 18) + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["const", 0]]
w_out = P(a0, PC_OUT, 9) + P(a0, CTX_OUT, 18) + P(a0, MEM_OUT, 18) + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["pv", a0, STATUS]]
for k in range(len(ia["cached"])):
    w_in += C(k); w_out += C(k)
used_a = {s[2] for s in w_in + w_out if s[0] == "pv"}
pv_const_a = [[a0, j, ia["public_values"][a0][j]] for j in range(105) if j not in used_a]
for n in wasm_names:
    assert pv_group(I[n]) == ga
    for (_, j, v) in pv_const_a:
        assert I[n]["public_values"][a0][j] == v

# ---------------- lane B
fi, fs = I["state_if"], I["state_seg0"]
gi, gs = pv_group(fi), pv_group(fs)
bi, bs = gi[0], gs[0]
assert len(fi["public_values"][bi]) == 70 and len(fs["public_values"][bs]) == 53
assert not fi["cached"] and len(fs["cached"]) == 1

# ---------------- lane F
fe, fr = I["rt_enter"], I["rt_resume"]
assert [len(v) for v in fe["public_values"]] == [816] and not fe["cached"]
# lane F's prover gives each AIR as many public values as its constraints read: ENT reads B_in (408)
# and B_out's first 408 bytes; B_out's Wasm part (376 B, "out free" in BndLay) is not in the proof
RX = [len(v) for v in fr["public_values"]].index(1439)
assert [c[1] for c in fr["cached"]] == ["TAPE", "XTAPE"]
ENG, CALL, R_BIN, R_BOUT = 408, 784, 247, 247 + 784
T_OFF, T_W = 75, 8  # BndRec `t` (engF offset 75, u64)
eq_bytes = [j for j in range(ENG) if not (T_OFF <= j < T_OFF + T_W)]

# ---------------- lane G
gI, gF = I["init"], I["final"]
iI = [len(v) for v in gI["public_values"]].index(44)
gfin = pv_group(gF); iF = gfin[0]
assert len(gF["public_values"][iF]) == 58 and [len(gF["public_values"][a]) for a in gfin[1:]] == [30] * 4
assert not gI["cached"] and not gF["cached"]
ctx_src = lambda a: P(a, 0, 14) + Z(4)

# ---------------- phase codes: M9_PHASES=view (default; lane E M11i / TreeM8.lean: View.split codes
# init 0, eng 1, call 6, done 4 -- the pq-e2e-m9 circuit) or m8 (the pq-e2e-m8 circuit: init 1, mid 3, done 2)
PH = {"view": {"init": 0, "eng": 1, "call": 6, "done": 4}, "m8": {"init": 1, "eng": 3, "call": 3, "done": 2}}[os.environ.get("M9_PHASES", "view")]

# ---------------- record regions
REGIONS = [
    ("W", len(w_in), "lane A Wasm boundary fields + CODE/FUNC roots"),
    ("S", 88, "lane B: prev root 16 | wsLen | cur root 18 | target R_n 18 | post root 16 | change count | HTAPE root 18"),
    ("G", 14, "INIT ctxRoot = ctxD(.raw cb wb)"),
    ("E", ENG, "RT_ENTER B_in (BndRec.encode, eng)"),
    ("C", len(eq_bytes), "call record bytes RT_ENTER B_out = RT_RESUME B_in (all but t)"),
    ("Tpre", T_W, "RT_ENTER B_out t"),
    ("Tfin", T_W, "RT_RESUME B_in t"),
    ("Wfin", CALL - ENG, "RT_RESUME B_in Wasm part (lane A's fin r record)"),
    ("Q", ENG, "RT_RESUME B_out (BndRec.encode, eng)"),
    ("X", R_BIN, "RT_RESUME env / receipt-state totals in, out (RX public values 0..247)"),
    ("XT", 36, "RT_RESUME TAPE / XTAPE roots (public stand-in tapes)"),
    ("F", 14, "FINAL finInDigest = bdigest(0x46 || FinIn)"),
]
OFF, o = {}, 0
for n, w, _ in REGIONS:
    OFF[n] = (o, w); o += w
N_REC = o
W_ = lambda n: OFF[n][1]

def tmpl(name, pin, pout, touch_in, touch_out, **kw):
    """touch_*: {region: sources}; every other region passes through (pass slots in region order)."""
    rin, rout, n_pass = [], [], 0
    for r, w, _ in REGIONS:
        if r in touch_in or r in touch_out:
            if pin != PH['init']:
                rin += touch_in.get(r) or [["pass", n_pass + j] for j in range(w)]
            if pout != PH['done']:
                rout += touch_out.get(r) or [["pass", n_pass + j] for j in range(w)]
            if not (touch_in.get(r) and touch_out.get(r)) and not (pin == PH['init'] or pout == PH['done']):
                n_pass += w
        else:
            if pin != PH['init']:
                rin += [["pass", n_pass + j] for j in range(w)]
            if pout != PH['done']:
                rout += [["pass", n_pass + j] for j in range(w)]
            if not (pin == PH['init'] or pout == PH['done']):
                n_pass += w
    t = {"name": name, "phase_in": pin, "phase_out": pout, "rec_in": rin, "rec_out": rout, "n_pass": n_pass,
         "stmt_len": 0, "pv_equal": [], "pv_const": [], "ctx": "witness"}
    t.update(kw)
    return t

# INIT free cells and FINAL dropped cells live in one private witness vector `stmt` (both leaves
# witness it; nothing ties INIT's copy to FINAL's): [INIT free | FINAL drop]
FREE_AT_INIT = ["W", "E", "Tfin", "Wfin", "F"]
n_free = sum(W_(r) for r in FREE_AT_INIT)
free_off, k = {}, 0
for r in FREE_AT_INIT:
    free_off[r] = k; k += W_(r)
st = lambda lo, n: [["stmt", lo + j] for j in range(n)]
STMT_LEN = n_free + N_REC

init_out = {r: st(free_off[r], W_(r)) for r in FREE_AT_INIT}
init_out["S"] = P(iI, 28, 16) + Z(88 - 16)
init_out["G"] = P(iI, 14, 14)
for r in ["C", "Tpre", "Q", "X", "XT"]:
    init_out[r] = Z(W_(r))
# FINAL: every region read into dropped witness cells, except F = finInDigest (pv 14..28), and S's
# cur / target read from the same cells (lane B: last R_out = IF's R_n)
fin_in = {}
for r, w, _ in REGIONS:
    fin_in[r] = st(n_free + OFF[r][0], w)
s0 = n_free + OFF["S"][0]
fin_in["S"] = st(s0, 17) + st(s0 + 17, 18) + st(s0 + 17, 18) + st(s0 + 53, 35)
fin_in["F"] = P(iF, 14, 14)

if_in = P(bi, 0, 16) + Z(88 - 16)
if_out = P(bi, 0, 16) + P(bi, 16, 1) + P(bi, 17, 18) + P(bi, 35, 18) + P(bi, 53, 16) + P(bi, 69, 1) + Z(18)

templates = [
    tmpl("INIT", PH["init"], PH["eng"], {}, init_out, stmt_len=STMT_LEN, ctx=ctx_src(iI)),
    tmpl("STATE_IF", PH["eng"], PH["eng"], {"S": if_in}, {"S": if_out}, pv_equal=[gi]),
    tmpl("RT_ENTER", PH["eng"], PH["call"], {"E": P(0, 0, ENG), "C": Z(W_("C")), "Tpre": Z(T_W)},
         {"E": Z(ENG), "C": [["pv", 0, ENG + j] for j in eq_bytes], "Tpre": P(0, ENG + T_OFF, T_W)}),
    tmpl("WASM", PH["call"], PH["call"], {"W": w_in}, {"W": w_out}, pv_equal=[ga] if len(ga) > 1 else [], pv_const=pv_const_a),
    tmpl("RT_RESUME", PH["call"], PH["eng"],
         {"C": [["pv", RX, R_BIN + j] for j in eq_bytes], "Tfin": P(RX, R_BIN + T_OFF, T_W), "Wfin": P(RX, R_BIN + ENG, CALL - ENG),
          "Q": Z(ENG), "X": Z(R_BIN), "XT": Z(36)},
         {"C": Z(W_("C")), "Tfin": Z(T_W), "Wfin": Z(CALL - ENG), "Q": P(RX, R_BOUT, ENG), "X": P(RX, 0, R_BIN), "XT": C(0) + C(1)}),
    None,  # STATE_SEG, below (its S part keeps target / post / change count)
    tmpl("FINAL", PH["eng"], PH["done"], fin_in, {}, stmt_len=STMT_LEN, ctx=ctx_src(iF), pv_equal=[gfin],
         pv_const=[[iF, j, gF["public_values"][iF][j]] for j in range(28, 58)]),
]
# STATE_SEG: S = prev, wsLen, cur (R_in -> R_out) from its pv; target, post, change count carried
# (pass); HTAPE root out. Built by hand: a region touched partly.
sg = tmpl("STATE_SEG", PH["eng"], PH["eng"], {"S": Z(88)}, {"S": Z(88)}, pv_equal=[gs])
# rebuild S with partial pass slots appended after the template's other pass slots
np0 = sg["n_pass"]
pas = lambda lo, n: [["pass", np0 + lo + j] for j in range(n)]
sS_in = P(bs, 0, 16) + P(bs, 16, 1) + P(bs, 17, 18) + pas(0, 18) + pas(18, 16) + pas(34, 1) + Z(18)
sS_out = P(bs, 0, 16) + P(bs, 16, 1) + P(bs, 35, 18) + pas(0, 18) + pas(18, 16) + pas(34, 1) + C(0)
o_s = OFF["S"][0]
sg["rec_in"][o_s:o_s + 88] = sS_in
sg["rec_out"][o_s:o_s + 88] = sS_out
sg["n_pass"] = np0 + 35
templates[5] = sg

# ---------------- leaves and the native chain (the driver re-checks it)
order = [("INIT", "init"), ("STATE_IF", "state_if"), ("RT_ENTER", "rt_enter")] + [("WASM", n) for n in wasm_names] + \
        [("RT_RESUME", "rt_resume"), ("STATE_SEG", "state_seg0"), ("FINAL", "final")]
tm = {t["name"]: t for t in templates}
stmt = [None] * STMT_LEN

def val(info, src, cur, t):
    k = src[0]
    if k == "pv": return info["public_values"][src[1]][src[2]]
    if k == "cached": return info["cached"][src[1]][2][src[2]]
    if k == "const": return src[1]
    if k == "stmt": return stmt[src[1]]
    if k == "pass":
        p = t["rec_in"].index(src)
        return cur[p]
    raise ValueError(src)

# INIT free values: what each consumer reads
need = {"W": [val(ia, s, None, None) for s in w_in],
        "E": fe["public_values"][0][:ENG],
        "Tfin": fr["public_values"][RX][R_BIN + T_OFF:R_BIN + T_OFF + T_W],
        "Wfin": fr["public_values"][RX][R_BIN + ENG:R_BIN + CALL],
        "F": gF["public_values"][iF][14:28]}
for r in FREE_AT_INIT:
    stmt[free_off[r]:free_off[r] + W_(r)] = need[r]
cur = None
for name, d in order:
    t, info = tm[name], I[d]
    if t["phase_in"] != PH["init"]:
        if name == "FINAL":  # the dropped cells take the record's values
            for p, s in enumerate(t["rec_in"]):
                if s[0] == "stmt":
                    if stmt[s[1]] is not None and stmt[s[1]] != cur[p]:
                        raise SystemExit(f"M9 chain: FINAL cell {p} (shared witness) {cur[p]} != {stmt[s[1]]} (lane B: last R_out != R_n?)")
                    stmt[s[1]] = cur[p]
        rin = [val(info, s, cur, t) for s in t["rec_in"]]
        bad = [p for p in range(N_REC) if rin[p] != cur[p]]
        if bad:
            reg = [n for n, (lo, w) in OFF.items() if lo <= bad[0] < lo + w]
            raise SystemExit(f"M9 chain: leaf {name} ({d}) B_in cell {bad[0]} (region {reg}) {rin[bad[0]]} != {cur[bad[0]]} ({len(bad)} cells)")
    if t["phase_out"] != PH["done"]:
        nxt = [None] * N_REC
        for p, s in enumerate(t["rec_out"]):
            nxt[p] = val(info, s, cur, t) if s[0] != "pass" else cur[t["rec_in"].index(s)]
        cur = nxt
# drop cells FINAL does not read (F is bound to its pv; S's target shares cur's cells) stay 0
stmt = [0 if x is None else x for x in stmt]
# ctx check (claimDigest of S)
claim = open(os.environ.get("T1_CLAIM", "/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3/claim.bin"), "rb").read()
secb = open(os.environ.get("T1_SECB", "/data/illia/nearproof-deps/e2e-t1/run3/secB.bin"), "rb").read()
assert claim.count(secb) == 1
i = claim.find(secb)
claim_s = claim[:i] + b"\0\0\0\0" + claim[i + len(secb):]
d = hashlib.sha384(claim_s).digest()[:42]
limbs = [65536 * d[3 * j] + 256 * d[3 * j + 1] + d[3 * j + 2] for j in range(14)]
assert gI["public_values"][iI][:14] == limbs == gF["public_values"][iF][:14], "INIT / FINAL claimDigest != bdigest(S)"
assert list(fe["public_values"][0][:42]) == list(d) == list(fr["public_values"][RX][R_BIN:R_BIN + 42]), "rt claimDigest bytes"

edges = {
    "INIT->STATE_IF": {"bound": ["S.prev_state_root (INIT pv 28..44 = WSB pv 0..15)"], "free_introduced": [f"{r} ({W_(r)})" for r in FREE_AT_INIT]},
    "STATE_IF->RT_ENTER": {"bound": [], "free": ["E: RT_ENTER B_in (408 B, eng record): no leaf exposes the BndRec of eng I c"]},
    "RT_ENTER->WASM0": {"bound": [], "free": ["W: lane A entry state (seam .pre -> .ent, C7 PREP)"], "carried": ["C (400 B)", "Tpre"]},
    "WASM0->WASM1": {"bound": ["W: lane A boundary fields + CODE/FUNC roots"]},
    "WASM1->RT_RESUME": {"bound": ["C: 400 B of the call record (from RT_ENTER B_out, carried)"], "free": ["Tfin (t)", "Wfin (376 B Wasm part, lane A fin r record)"], "dropped_later": ["W (lane A final state)", "Tpre"]},
    "RT_RESUME->STATE_SEG": {"bound": [], "dropped_later": ["Q: RT_RESUME B_out (eng record)", "X: RX env / totals", "XT: TAPE / XTAPE roots"]},
    "STATE_SEG->FINAL": {"bound": ["S: last R_out = IF R_n (FINAL leaf, shared witness cell)"], "free": ["F: finInDigest (FinIn not opened by lane B; FINB bus = joint leaf)"], "dropped": ["W", "S (rest)", "G", "Tpre", "Q", "X", "XT", "C/E/Tfin/Wfin (zero)"]},
}
spec = {"arity": ARITY, "depth": DEPTH, "n_rec": N_REC, "stmt": stmt, "claim_s_hex": claim_s.hex(), "templates": templates,
        "leaves": [{"template": n, "dir": str(T / d)} for n, d in order],
        "regions": [{"name": n, "offset": OFF[n][0], "cells": w, "what": why} for n, w, why in REGIONS],
        "edges": edges, "free_at_init": FREE_AT_INIT,
        "scope": "E2E-D M9 prototype: heterogeneous tree over real T1 leaves only (lanes G INIT/FINAL, B STATE_IF/STATE_SEG, F RT enter/resume, A WASM segments), arity / depth per spec, wrap zk = 6; boundary record = lane D prototype regions (BndRec bytes only between the rt leaves), free / dropped cells listed in spec.edges"}
json.dump(spec, open(W / "spec.json", "w"))
print(f"M9_SPEC n_rec={N_REC} regions={[(n, w) for n, w, _ in REGIONS]} stmt(private: free {n_free} + dropped {N_REC})={STMT_LEN} "
      f"leaves={[n for n, _ in order]} pv groups A={ga} IF={gi} SEG={gs} FINAL={gfin} claimDigest={d.hex()[:8]}..{d.hex()[-6:]}")
for e, v in edges.items():
    print(f"M9_EDGE {e}: {json.dumps(v)}")
