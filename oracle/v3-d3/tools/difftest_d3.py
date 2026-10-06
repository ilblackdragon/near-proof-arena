#!/usr/bin/env python3
"""Full-runtime difftest of RuntimeD3: the Lean checker `nearspec-v3-check-d3` (checkD3) vs
nearcore's verdicts in a D3 corpus (oracle/v3-d3; meta.json `expected_rel` = nearcore, `in_d3`).

  difftest_d3.py CORPUS [--sample N] [--shards K] [--only d3|mutants|ood]

A case disagrees when (in D3α by the oracle) the Lean verdict differs from nearcore (accept vs
reject), or when Lean says out_of_domain for an in-D3α case (or vice versa for honest out-of-D3
cases Lean accepts). Prints counts by family and up to 20 disagreements."""
import json, os, subprocess, sys, collections, random
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("D3_CHECK", os.path.join(HERE, "../../wasm-d3/lean/.lake/build/bin/nearspec-v3-check-d3"))

def main():
    corpus = sys.argv[1]
    arg = lambda n, d: sys.argv[sys.argv.index(n) + 1] if n in sys.argv else d
    sample = int(arg("--sample", "0")); shards = int(arg("--shards", "8")); only = arg("--only", "")
    dirs = []
    for fam in ("d3", "mutants", "ood"):
        if only and fam != only: continue
        p = os.path.join(corpus, fam)
        if os.path.isdir(p):
            dirs += [os.path.join(p, d) for d in sorted(os.listdir(p))]
    if sample and sample < len(dirs):
        random.Random(1).shuffle(dirs); dirs = sorted(dirs[:sample])
    import tempfile
    got = {}
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for s in range(shards):
            part = dirs[s::shards]
            if part:
                f = open(os.path.join(td, f"o{s}"), "w")
                procs.append((subprocess.Popen([LEAN] + part, stdout=f, text=True), f))
        for p, f in procs:
            p.wait(); f.close()
        for s in range(shards):
            fn = os.path.join(td, f"o{s}")
            if os.path.exists(fn):
                for line in open(fn):
                    j = json.loads(line); got[j["case"]] = j
    stats = collections.Counter(); bad = []
    for d in dirs:
        m = json.load(open(os.path.join(d, "meta.json")))
        fam = os.path.basename(os.path.dirname(d))
        g = got.get(d, {"verdict": "missing", "reason": ""})
        v = g["verdict"]; near = m.get("expected_rel")
        ind3 = m.get("in_d3", m.get("expected_rel_d3") is not None and not m.get("d3_violations"))
        stats[(fam, v, "nearcore_ok" if near else "nearcore_rej")] += 1
        if v == "out_of_domain":
            if ind3 and fam != "ood":
                bad.append((d, "lean out_of_domain on an in-D3α case", g["reason"], m.get("nearcore")))
            continue
        if v == "missing" or (v == "accept") != bool(near):
            if fam == "ood" and v != "missing":
                stats[("ood_decided_by_lean", v, str(near))] += 1
                if (v == "accept") != bool(near):
                    bad.append((d, f"lean {v} vs nearcore {near} (oracle: out of D3α)", g["reason"], m.get("nearcore")))
                continue
            bad.append((d, f"lean {v} vs nearcore {near}", g["reason"], m.get("nearcore")))
    for k, c in sorted(stats.items()): print(k, c)
    print(f"cases={len(dirs)} disagreements={len(bad)}")
    for b in bad[:20]: print("DISAGREE", *b, sep="\n  ")
    sys.exit(1 if bad else 0)

main()
