#!/usr/bin/env python3
"""E2E-D M8: the heterogeneous-tree spec over the lanes' own saved T1 leaves (m8_import_real.sh).

    m8_spec_real.py WORK ARITY DEPTH     reads WORK/tmpl/{wasm0,wasm1,state_if,state_seg0}/INFO.json

Leaves: INIT (stub) | STATE_IF (lane B B-T1 intake/finalize leaf) | WASM x2 (lane A A-T1 pinned
segments) | STATE_SEG (lane B state segment) | FINAL (stub) | PAD.
Boundary record (prototype schema, see m8_spec.py; lane E's BndRec digests replace it):
  W part (85): lane A's in/out boundary fields, depth/nblk/mem, halted, CODE + FUNC roots
  S part (88): prev_state_root (16) | wsLen | cur working-set root (18) | target root R_n (18) |
               post_state_root (16) | change count | HTAPE root (18)
Lane B public values (Tmpl.lean, leaf_chain.py): 0-15 prev root, 16 wsLen, 17-34 root A,
35-52 root B, 53-68 post root (IF), 69 change count (IF). IF: A = R_0, B = R_n; seg: A = R_in,
B = R_out. FINAL reads `cur` and `target` from the same statement cells, so the chain forces the
last segment's R_out = IF's R_n (leaf_chain.py's check, in-circuit).
"""
import hashlib, json, os, sys
from pathlib import Path

W, ARITY, DEPTH = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
T = W / "tmpl"
wasm_dirs = sorted(p for p in T.glob("wasm*") if (p / "INFO.json").exists())
infos = [json.load(open(d / "INFO.json")) for d in wasm_dirs]
fi = json.load(open(T / "state_if" / "INFO.json"))
fs = json.load(open(T / "state_seg0" / "INFO.json"))

def pv_group(info):
    g = [a for a, v in enumerate(info["public_values"]) if v]
    g.sort(key=lambda a: -len(info["public_values"][a]))
    v0 = info["public_values"][g[0]]
    for a in g:
        v = info["public_values"][a]
        assert v == v0[:len(v)], "an AIR's public values are not a prefix of the longest"
    return g

# ---- lane A (as m8_spec.py)
PC_IN, PC_OUT, CTX_IN, CTX_OUT, MEM_IN, MEM_OUT = 11, 21, 31, 49, 67, 85
STATUS, MEMSZ, DEPTH_P, NBLK = 8, 9, 103, 104
ga = pv_group(infos[0]); a0 = ga[0]
npub_a = len(infos[0]["public_values"][a0]); assert npub_a == 105
w_in = [["pv", a0, PC_IN + j] for j in range(9)] + [["pv", a0, CTX_IN + j] for j in range(18)] + \
       [["pv", a0, MEM_IN + j] for j in range(18)] + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["const", 0]]
w_out = [["pv", a0, PC_OUT + j] for j in range(9)] + [["pv", a0, CTX_OUT + j] for j in range(18)] + \
        [["pv", a0, MEM_OUT + j] for j in range(18)] + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["pv", a0, STATUS]]
for k in range(len(infos[0]["cached"])):
    w_in += [["cached", k, l] for l in range(18)]
    w_out += [["cached", k, l] for l in range(18)]
used_a = {s[2] for s in w_in + w_out if s[0] == "pv"}
pv_const_a = [[a0, j, infos[0]["public_values"][a0][j]] for j in range(npub_a) if j not in used_a]
for i in infos:
    assert pv_group(i) == ga
    for (_, j, v) in pv_const_a:
        assert i["public_values"][a0][j] == v
nW = len(w_in)

# ---- lane B
gi, gs = pv_group(fi), pv_group(fs)
bi, bs = gi[0], gs[0]
assert len(fi["public_values"][bi]) == 70 and len(fs["public_values"][bs]) == 53
assert not fi["cached"] and len(fs["cached"]) == 1, (fi["cached"], fs["cached"])
P = lambda a, lo, n: [["pv", a, lo + j] for j in range(n)]
Z = lambda n: [["const", 0]] * n
# S part = prev(16) wsLen(1) cur(18) target(18) post(16) nchg(1) htape(18)
nS = 16 + 1 + 18 + 18 + 16 + 1 + 18
if_in = P(bi, 0, 16) + Z(nS - 16)
if_out = P(bi, 0, 16) + P(bi, 16, 1) + P(bi, 17, 18) + P(bi, 35, 18) + P(bi, 53, 16) + P(bi, 69, 1) + Z(18)
pas = lambda lo, n: [["pass", lo + j] for j in range(n)]
# state segment: W part pass-through (slots 0..nW), target/post/nchg pass-through (slots nW..)
sg_in = P(bs, 0, 16) + P(bs, 16, 1) + P(bs, 17, 18) + pas(nW, 18) + pas(nW + 18, 16) + pas(nW + 34, 1) + Z(18)
sg_out = P(bs, 0, 16) + P(bs, 16, 1) + P(bs, 35, 18) + pas(nW, 18) + pas(nW + 18, 16) + pas(nW + 34, 1) + [["cached", 0, l] for l in range(18)]

def val(info, src):
    if src[0] == "pv":
        return info["public_values"][src[1]][src[2]]
    if src[0] == "cached":
        return info["cached"][src[1]][2][src[2]]
    if src[0] == "const":
        return src[1]
    raise ValueError(src)

# stub statement cells: W_init | prev_root | W_final | S_final (cur = target share cells)
w_init = [val(infos[0], s) for s in w_in]
w_final = [val(infos[-1], s) for s in w_out]
prev = [val(fi, s) for s in if_out[:16]]
s_if = [val(fi, s) for s in if_out]
s_sg = [val(fs, s) for s in sg_out[:35]]  # prev, wsLen, cur = R_out
target = s_if[35:53]
assert s_sg[17:35] == target, "lane B chain: last R_out != IF's R_n"
assert s_sg[:17] == s_if[:17], "lane B chain: prev root / wsLen differ"
s_fin = s_if[:17] + target + target + s_if[53:70] + [val(fs, s) for s in sg_out[70:]]
S = w_init + prev + w_final + s_fin
o_prev, o_wf, o_sf = nW, nW + 16, 2 * nW + 16
st = lambda lo, n: [["stmt", lo + j] for j in range(n)]
fin_s = st(o_sf, 17) + st(o_sf + 17, 18) + st(o_sf + 17, 18) + st(o_sf + 53, 17) + st(o_sf + 70, 18)
assert len(fin_s) == nS
templates = [
    {"name": "INIT", "phase_in": 1, "phase_out": 3, "rec_in": [], "rec_out": st(0, nW) + st(o_prev, 16) + Z(nS - 16),
     "stmt_len": len(S), "n_pass": 0, "pv_equal": [], "pv_const": []},
    {"name": "STATE_IF", "phase_in": 3, "phase_out": 3, "rec_in": pas(0, nW) + if_in, "rec_out": pas(0, nW) + if_out,
     "stmt_len": 0, "n_pass": nW, "pv_equal": [gi], "pv_const": []},
    {"name": "WASM", "phase_in": 3, "phase_out": 3, "rec_in": w_in + pas(0, nS), "rec_out": w_out + pas(0, nS),
     "stmt_len": 0, "n_pass": nS, "pv_equal": [ga] if len(ga) > 1 else [], "pv_const": pv_const_a},
    {"name": "STATE_SEG", "phase_in": 3, "phase_out": 3, "rec_in": pas(0, nW) + sg_in, "rec_out": pas(0, nW) + sg_out,
     "stmt_len": 0, "n_pass": nW + 35, "pv_equal": [gs], "pv_const": []},
    {"name": "FINAL", "phase_in": 3, "phase_out": 2, "rec_in": st(o_wf, nW) + fin_s, "rec_out": [],
     "stmt_len": len(S), "n_pass": 0, "pv_equal": [], "pv_const": []},
]
for t in templates:
    t["ctx"] = "witness"
leaves = [{"template": "INIT"}, {"template": "STATE_IF", "dir": str(T / "state_if")}] + \
         [{"template": "WASM", "dir": str(d)} for d in wasm_dirs] + \
         [{"template": "STATE_SEG", "dir": str(T / "state_seg0")}, {"template": "FINAL"}]
claim = open(os.environ.get("T1_CLAIM", "/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3/claim.bin"), "rb").read()
secb = open(os.environ.get("T1_SECB", "/data/illia/nearproof-deps/e2e-t1/run3/secB.bin"), "rb").read()
assert claim.count(secb) == 1
i = claim.find(secb)
claim_s = claim[:i] + b"\0\0\0\0" + claim[i + len(secb):]
cd = hashlib.sha384(claim_s).hexdigest()[:84]
assert len(claim_s) == 1007 and cd == "bb5aad11ba6ba32d91739f13a2dbd544f2420d770bcd2c3fde9ddc0e1c02710caee28e5e9e4e299f2f01"
spec = {"arity": ARITY, "depth": DEPTH, "n_rec": nW + nS, "stmt": S, "claim_s_hex": claim_s.hex(), "templates": templates, "leaves": leaves}
json.dump(spec, open(W / "spec.json", "w"))
print(f"M8_SPEC_REAL n_rec={nW + nS} (W {nW}, S {nS}) stub_stmt={len(S)} claim S={len(claim_s)} B claimDigest={cd[:8]}..{cd[-6:]} "
      f"leaves={[l['template'] for l in leaves]} pv groups A={ga} IF={gi} SEG={gs}")
