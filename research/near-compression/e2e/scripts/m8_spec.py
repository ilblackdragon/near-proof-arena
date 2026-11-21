#!/usr/bin/env python3
"""E2E-D M8 prototype: the heterogeneous-tree spec for T1-shaped segments.

    m8_spec.py WORK ARITY DEPTH      reads WORK/tmpl/{wasm0,wasm1,..,state}/INFO.json, writes WORK/spec.json

The boundary record (prototype schema; lane E's BndRec digests replace it, see README §0):
  W part (lane A's Wasm boundary): pc, t, S, sb, cid, S_seg, segb (3 limbs) | ctxDigest (18) |
         memRoot (18) | depth, nblk, mem | halted | every cached commitment of the segment proof
         (CODE, FUNC, ...: 18 limbs each)
  S part (lane B's state):          prev_state_root (16) | wsLen | every cached commitment of the
         state proof (TAPE, HTAPE: 18 limbs each)
Templates:
  INIT  (no child, statement S):  INIT -> MID, B_out = (S.W_init, S.prev_root, wsLen 0, roots 0)
  WASM  (lane A segment):         MID -> MID, W part from the segment's in / out public values and
         cached roots (halted = 0 on input), S part passed through
  STATE (lane B state proof):     MID -> MID, S part (prev root; on output wsLen and the TAPE /
         HTAPE roots), W part passed through
  FINAL (no child, statement S):  MID -> DONE, B_in = (S.W_final, S.S_final)
S = W_init | prev_root | W_final | S_final.
Every public value of a child is bound (record, equal-group, or pinned constant); htree's
TemplateSpec::check refuses the spec otherwise.
"""
import json, sys
from pathlib import Path

W, ARITY, DEPTH = Path(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
T = W / "tmpl"
wasm_dirs = sorted(p for p in T.glob("wasm*") if (p / "INFO.json").exists())
assert wasm_dirs, "no lane A segment proofs"
state_dir = T / "state"
infos = [json.load(open(d / "INFO.json")) for d in wasm_dirs]
sinfo = json.load(open(state_dir / "INFO.json"))

# ---- lane A layout (seg.rs: PUB_*; wasmBaseSegAirMP, 105 public values)
PC_IN, PC_OUT, CTX_IN, CTX_OUT, MEM_IN, MEM_OUT = 11, 21, 31, 49, 67, 85
STATUS, MEMSZ, DEPTH_P, NBLK = 8, 9, 103, 104
def pv_group(info):
    g = [a for a, v in enumerate(info["public_values"]) if v]
    v0 = info["public_values"][g[0]]
    assert all(info["public_values"][a] == v0 for a in g), "AIRs reading the public values disagree"
    return g
ga = pv_group(infos[0])
assert all(pv_group(i) == ga for i in infos)
npub_a = len(infos[0]["public_values"][ga[0]])
assert npub_a == 105, npub_a
a0 = ga[0]
w_in = [["pv", a0, PC_IN + j] for j in range(9)] + [["pv", a0, CTX_IN + j] for j in range(18)] + \
       [["pv", a0, MEM_IN + j] for j in range(18)] + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["const", 0]]
w_out = [["pv", a0, PC_OUT + j] for j in range(9)] + [["pv", a0, CTX_OUT + j] for j in range(18)] + \
        [["pv", a0, MEM_OUT + j] for j in range(18)] + [["pv", a0, DEPTH_P], ["pv", a0, NBLK], ["pv", a0, MEMSZ], ["pv", a0, STATUS]]
n_cached_a = len(infos[0]["cached"])
for k in range(n_cached_a):
    w_in += [["cached", k, l] for l in range(18)]
    w_out += [["cached", k, l] for l in range(18)]
used_a = {s[2] for s in w_in + w_out if s[0] == "pv"}
pv_const_a = [[a0, j, infos[0]["public_values"][a0][j]] for j in range(npub_a) if j not in used_a]
for i in infos:
    for (_, j, v) in pv_const_a:
        assert i["public_values"][a0][j] == v, "an unused public value differs between segments"
nW = len(w_in)

# ---- lane B layout (17 public values: prev_state_root as 16 limbs, wsLen)
gb = pv_group(sinfo)
b0 = gb[0]
npub_b = len(sinfo["public_values"][b0])
assert npub_b == 17, npub_b
n_cached_b = len(sinfo["cached"])
s_in = [["pv", b0, j] for j in range(16)] + [["const", 0]] + [["const", 0]] * (18 * n_cached_b)
s_out = [["pv", b0, j] for j in range(16)] + [["pv", b0, 16]]
for k in range(n_cached_b):
    s_out += [["cached", k, l] for l in range(18)]
nS = len(s_in)
n_rec = nW + nS

def val(info, src):
    if src[0] == "pv":
        return info["public_values"][src[1]][src[2]]
    if src[0] == "cached":
        return info["cached"][src[1]][2][src[2]]
    if src[0] == "const":
        return src[1]
    raise ValueError(src)

# ---- the statement S
w_init = [val(infos[0], s) for s in w_in]
w_final = [val(infos[-1], s) for s in w_out]
prev_root = [val(sinfo, s) for s in s_in[:16]]
s_final = [val(sinfo, s) for s in s_out]
S = w_init + prev_root + w_final + s_final
o_prev, o_wf, o_sf = nW, nW + 16, nW + 16 + nW

def stmt(lo, n):
    return [["stmt", lo + i] for i in range(n)]

templates = [
    {"name": "INIT", "phase_in": 1, "phase_out": 3, "rec_in": [],
     "rec_out": stmt(0, nW) + stmt(o_prev, 16) + [["const", 0]] * (1 + 18 * n_cached_b),
     "stmt_len": len(S), "n_pass": 0, "pv_equal": [], "pv_const": []},
    {"name": "WASM", "phase_in": 3, "phase_out": 3,
     "rec_in": w_in + [["pass", j] for j in range(nS)], "rec_out": w_out + [["pass", j] for j in range(nS)],
     "stmt_len": 0, "n_pass": nS, "pv_equal": [ga] if len(ga) > 1 else [], "pv_const": pv_const_a},
    {"name": "STATE", "phase_in": 3, "phase_out": 3,
     "rec_in": [["pass", j] for j in range(nW)] + s_in, "rec_out": [["pass", j] for j in range(nW)] + s_out,
     "stmt_len": 0, "n_pass": nW, "pv_equal": [gb] if len(gb) > 1 else [], "pv_const": []},
    {"name": "FINAL", "phase_in": 3, "phase_out": 2, "rec_in": stmt(o_wf, nW) + stmt(o_sf, nS), "rec_out": [],
     "stmt_len": len(S), "n_pass": 0, "pv_equal": [], "pv_const": []},
]
leaves = [{"template": "INIT"}] + [{"template": "WASM", "dir": str(d)} for d in wasm_dirs] + \
         [{"template": "STATE", "dir": str(state_dir)}, {"template": "FINAL"}]
spec = {"arity": ARITY, "depth": DEPTH, "n_rec": n_rec, "stmt": S, "templates": templates, "leaves": leaves}
json.dump(spec, open(W / "spec.json", "w"))
print(f"M8_SPEC n_rec={n_rec} (W {nW}: lane A cached {n_cached_a} [{', '.join(c[1] for c in infos[0]['cached'])}]; "
      f"S {nS}: lane B cached {n_cached_b} [{', '.join(c[1] for c in sinfo['cached'])}]) stmt={len(S)} "
      f"leaves={[l['template'] for l in leaves]} lane A pv groups={ga} pinned={len(pv_const_a)} lane B pv groups={gb}")
