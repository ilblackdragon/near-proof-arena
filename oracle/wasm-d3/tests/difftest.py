#!/usr/bin/env python3
"""D3α checkpoint-2 difftest: pinned nearcore (oracle/wasm-d3 harness) vs the Lean spec
(`NearSpecV3.Wasm`, driver oracle/wasm-d3/lean → `nearspec-v3-wasm`).

  difftest.py (opcodes | random N SEED | mutate N SEED) [--shards K]

Comparison is on full outcome lines (status, burnt, used, return bytes or exact error), with one
normalisation: the text of a `LinkError` for a mistyped import is wasmtime's message, which the spec
does not reproduce (`Rel_D3` identifies error kinds; the variant itself is compared). Lean outputs
`out-of-domain …` (not in `InD3α`, e.g. float contracts) are counted and excluded; `unmodeled …` is a
failure. Exit 1 on any disagreement or unmodeled case.
"""
import collections
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.environ.get("D3_HARNESS", "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")
LEAN = os.environ.get("D3_SPEC", os.path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-wasm"))


def norm(line):
    return re.sub(r'LinkError \{ msg: ".*" \}', lambda m: m.group(0) if "unknown or invalid import" in m.group(0)
                  else 'LinkError { msg: <incompatible> }', line.replace('"*incompatible import type*"', '"x"'))


def gen(argv):
    kind = argv[0]
    if kind == "opcodes":
        with tempfile.NamedTemporaryFile("r", suffix=".labels", delete=False) as lf:
            out = subprocess.run([sys.executable, os.path.join(HERE, "opcases.py"), lf.name],
                                 check=True, capture_output=True, text=True).stdout.splitlines()
            labels = open(lf.name).read().splitlines()
        return out, labels
    script = {"random": "gen_d3a.py", "mutate": "mutate.py"}[kind]
    out = subprocess.run([sys.executable, os.path.join(HERE, script), argv[1], argv[2]],
                         check=True, capture_output=True, text=True).stdout.splitlines()
    return out, [f"{kind}#{i}" for i in range(len(out))]


def main():
    args = sys.argv[1:]
    shards = 8
    if "--shards" in args:
        i = args.index("--shards")
        shards = int(args[i + 1])
        del args[i:i + 2]
    cases, labels = gen(args)
    n = len(cases)
    t0 = time.time()
    near = subprocess.run([HARNESS], input="\n".join(cases) + "\n", check=True,
                          capture_output=True, text=True).stdout.splitlines()
    t1 = time.time()
    with tempfile.TemporaryDirectory() as td:
        procs = []
        for k in range(shards):
            p = os.path.join(td, f"in{k}")
            with open(p, "w") as f:
                f.write("\n".join(cases[k::shards]) + "\n")
            procs.append(subprocess.Popen([LEAN], stdin=open(p), stdout=open(p + ".out", "w")))
        for pr in procs:
            pr.wait()
        outs = [open(os.path.join(td, f"in{k}.out")).read().splitlines() for k in range(shards)]
    t2 = time.time()
    lean = [None] * n
    for k in range(shards):
        for j, line in enumerate(outs[k]):
            lean[k + j * shards] = line
    assert len(near) == n and all(x is not None for x in lean), "missing outputs"
    cats = collections.Counter()
    bad = ood = unm = 0
    for i, (a, b) in enumerate(zip(near, lean)):
        if b.startswith("out-of-domain"):
            ood += 1
            continue
        if b.startswith("unmodeled"):
            unm += 1
            if unm <= 10:
                print(f"UNMODELED {labels[i]}: {b}  (nearcore: {a[:150]})")
            continue
        p = a.split(" ", 3)
        if p[0] == "ok":
            cats["ok"] += 1
        else:
            m = re.match(r"(\w+)(?:[({ ]+(\w+))?", p[3])
            cats[f"{m.group(1)}:{m.group(2) or ''}" if m else p[3][:40]] += 1
        if norm(a) != norm(b):
            bad += 1
            if bad <= 20:
                print(f"DISAGREE {labels[i]}: {cases[i][:100]}...\n  nearcore: {a[:300]}\n  spec    : {b[:300]}")
    print(f"family={' '.join(args)} cases={n} compared={n - ood - unm} out_of_domain={ood} unmodeled={unm} disagreements={bad}")
    print(f"nearcore {t1 - t0:.1f}s, spec {t2 - t1:.1f}s ({shards} shards)")
    for c, k in sorted(cats.items(), key=lambda x: -x[1]):
        print(f"  {k:6d}  {c}")
    sys.exit(1 if bad or unm else 0)


if __name__ == "__main__":
    main()
