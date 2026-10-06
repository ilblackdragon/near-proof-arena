#!/usr/bin/env python3
"""Per-receipt storage-proof limit (4,000,000 bytes) cases at and over the limit.

Builds `--limit-plan` transactions for `near-d3-ttn --v2` against the large values of s0big /
s1big (ttn2.wat op 6), calibrates the number of removes and the final small read so that the
receipt's recorded growth lands EXACTLY on 4,000,000 bytes (must pass) and 4,000,001 bytes (must
fail with RecordedStorageExceeded), plus clearly-under / clearly-over cases. The recorded growth is
measured by the Lean spec (`nearspec-v3-wasm --chunk --deltas`); the verdict is nearcore's (trace
expected columns) and is compared with the spec's by `difftest_ttn.py` on the final trace.

  limit_cases.py OUTDIR [--seed S]
"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, "target/debug/near-d3-ttn")
LEAN = os.path.join(HERE, "../wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm")
HEAVY = ["taskset", "-c", "8-15,24-31", "/data/illia/nearproof-deps/bin/heavy"]
LIMIT = 4_000_000
GAS = 300_000_000_000_000

def args_hex(bigs, removes, freads):
    ops = [[6, b, 0] for b in bigs] + [[3, 47, 0]] * removes + [[7, j, 0] for j in freads]
    return bytes(x for op in ops for x in op).hex()

def run(out, seed, plan, tag, blocks=20):
    pf = os.path.join(out, f"plan-{tag}.txt")
    open(pf, "w").write("\n".join(f"{r} {a} {h} {GAS}" for r, a, h in plan) + "\n")
    tr = os.path.join(out, f"{tag}.trace")
    subprocess.run(HEAVY + [BIN, "--v2", "--seed", str(seed), "--blocks", str(blocks), "--ops", "60",
                    "--limit-plan", pf, "--out", os.path.join(out, f"{tag}.json"), "--trace", tr],
                   check=True, stdout=open(os.path.join(out, f"{tag}.summary"), "w"),
                   stderr=subprocess.DEVNULL, env={**os.environ, "RUST_LOG": "error"})
    code = os.path.join(out, "code.hex")
    open(code, "w").write(open(os.path.join(HERE, "ttn2.wasm"), "rb").read().hex())
    lean = subprocess.run(HEAVY + [LEAN, "--chunk", code, "--deltas"], stdin=open(tr), check=True,
                          capture_output=True, text=True).stdout.splitlines()
    # locate each plan call: (status_nearcore, status_lean, delta)
    res, li = {}, 0
    for line in open(tr):
        t = line.split()
        n = int(t[2]); k = int(t[3 + n])
        for j in range(k):
            b = 4 + n + 17 * j
            got = lean[li]; li += 1
            for (r, a, h) in plan:
                if t[b] == a and t[b + 2] == h:
                    d = int(got.split(" d=")[1])
                    res[(a, h)] = (t[b + 3], got.split()[0], d)
    return res, tr

def main():
    out = sys.argv[1]; os.makedirs(out, exist_ok=True)
    seed = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 7
    targets = {"s0big": 0, "s1big": 1}             # 0: exactly the limit (must pass), 1: limit+1 (must fail)
    bigs = [0, 1, 2, 3, 4, 5, 6]                    # omit the largest value: ~3.93 MB
    groups = [16 * h for h in range(16)]            # record every "f" hi-nibble branch first
    fresh = [j for j in range(256) if j % 16]
    # A. big reads + group reads -> number of removes (+2000 each) leaving a gap of ~1-3 KB
    plan = [(6, a, args_hex(bigs, 0, groups)) for a in targets]
    res, _ = run(out, seed, plan, "calA")
    removes = {a: (LIMIT - res[(a, h)][2] - 2900) // 2000 for (_, a, h) in plan}
    print("removes:", removes)
    # B. one run, one candidate per round (each in its own chunk; the big accounts' subtree is
    # read-only, so every chunk starts from the same recording state): the base, and the base plus
    # one fresh small read f[j] for every j -> the recorded growth d_j of each
    plan, rounds = [], {}
    for a in targets:
        plan.append((4, a, args_hex(bigs, removes[a], groups)))
        for i, j in enumerate(fresh):
            plan.append((6 + i, a, args_hex(bigs, removes[a], groups + [j])))
    res, _ = run(out, seed, plan, "calB", blocks=len(fresh) + 12)
    final = []
    for a, plus in targets.items():
        tgt = LIMIT + plus
        base = res[(a, args_hex(bigs, removes[a], groups))][2]
        dj = {j: res[(a, args_hex(bigs, removes[a], groups + [j]))][2] for j in fresh}
        cost = {j: dj[j] - base for j in fresh}
        pick = None
        for j in fresh:                                  # one read
            if base + cost[j] == tgt:
                pick = [j]; break
        if pick is None:                                 # two reads (independent fresh leaves)
            for e in fresh:
                for j in fresh:
                    if j != e and base + cost[e] + cost[j] == tgt:
                        pick = [e, j]; break
                if pick:
                    break
        if pick is None:                                 # three reads
            want = {}
            for e in fresh:
                for j in fresh:
                    if e < j:
                        want.setdefault(cost[e] + cost[j], (e, j))
            for x in fresh:
                need = tgt - base - cost[x]
                if need in want and x not in want[need]:
                    pick = [x, *want[need]]; break
        print(f"{a}: base {base}, read costs {min(cost.values())}..{max(cost.values())}, pick {pick} for {tgt}")
        assert pick is not None
        final.append((6 if plus == 0 else 8, a, args_hex(bigs, removes[a], groups + pick)))
    final += [(12, "s0big", args_hex([0, 1, 2, 3, 4, 5], 0, [])),
              (14, "s1big", args_hex(list(range(8)), 0, [])),
              (16, "s0big", args_hex(list(range(8)), 5, [3]))]
    res, tr = run(out, seed, final, "final")
    for (r, a, h) in final:
        near, lean, d = res[(a, h)]
        print(f"round {r} {a}: recorded growth {d} (limit {LIMIT}) nearcore {near} spec {lean}")
    dt = subprocess.run(HEAVY + [sys.executable, os.path.join(HERE, "difftest_ttn.py"), tr, "--shards", "8",
                         "--code", os.path.join(HERE, "ttn2.wasm")], capture_output=True, text=True).stdout
    print(dt)

main()
