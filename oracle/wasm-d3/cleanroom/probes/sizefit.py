"""Fit the instrumented-size estimate from black-box prepared-module LENGTHS (harness `prepare` mode)."""
import sys, os, subprocess
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
import nearwasm as nw
from probe import near
S = sys.argv[1]
lines = open(S).read().splitlines()
out = near(lines, "prepare")
rows = []
for ln, o in zip(lines, out):
    if o.startswith("prepare-error"): continue
    w = bytes.fromhex(ln.split()[1])
    try: m = nw.prepare(w)
    except Exception: continue
    d = [f for f in m.funcs if not f.imported]
    feats = dict(orig=len(w), nf=len(d),
                 ncp=sum(1 for f in d for p in f.points if not p[2]),
                 cpl=sum(nw.sleb_len(p[1]) for f in d for p in f.points if not p[2]),
                 nlp=sum(1 for f in d for p in f.points if p[2]),
                 nret=sum(1 for f in d for o in f.ops if o[0] == 0x0F and f.live[f.ops.index(o)]),
                 pro=sum(nw.sleb_len(((f.frame + 7)//8)*nw.R) + nw.sleb_len(f.opmax+f.frame) for f in d))
    rows.append((len(o)//2, feats))
print(len(rows))
import json; json.dump(rows, open("/tmp/claude-1002/-data-illia-nearproof/29f86fd5-cfb7-44c7-996e-70d81e3d17a4/scratchpad/sizes.json","w"))
