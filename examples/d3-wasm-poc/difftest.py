#!/usr/bin/env python3
"""D3 PoC differential test: pinned nearcore (near-vm-runner, PV86, Wasmtime)
vs the Lean executable semantics (lean/ → `wasm-poc`).

  difftest.py N SEED [SHARDS]

Generates N cases with gen_wasm.py, runs both implementations on identical
bytes and compares full outcome lines (status, burnt gas, used gas, return data
or exact error). Exit 1 on any disagreement or any `unmodeled`/`unsupported`.
Both binaries must be built first (see README.md); run under
`taskset -c 8-15,24-31` on the shared host.
"""
import collections
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.environ.get(
    "D3_HARNESS", "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")
LEAN = os.environ.get("D3_LEAN", os.path.join(HERE, "lean/.lake/build/bin/wasm-poc"))


def main():
    n = int(sys.argv[1])
    seed = int(sys.argv[2])
    shards = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    cases = subprocess.run([sys.executable, os.path.join(HERE, "gen_wasm.py"), str(n), str(seed)],
                           check=True, capture_output=True, text=True).stdout.splitlines()
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
    bad = 0
    for i, (a, b) in enumerate(zip(near, lean)):
        parts = a.split(" ", 3)
        cat = parts[0] if parts[0] == "ok" else parts[3].split(" ")[0].split("(")[0] + ":" + parts[3].split("(")[1].split(" ")[0].rstrip(")")
        cats[cat] += 1
        if a != b:
            bad += 1
            if bad <= 20:
                print(f"DISAGREE case {i}: gas/hex = {cases[i][:120]}...")
                print(f"  nearcore: {a}")
                print(f"  lean    : {b}")
    print(f"cases={n} seed={seed} disagreements={bad}")
    print(f"nearcore {t1 - t0:.1f}s, lean {t2 - t1:.1f}s ({shards} shards)")
    for c, k in sorted(cats.items(), key=lambda x: -x[1]):
        print(f"  {k:6d}  {c}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
