#!/usr/bin/env python3
"""Op-level difftest of the trie-backed External (spec/lean/v3/NearSpecV3/Wasm/{TrieStore,
TrieAccounting,ChunkStorage}.lean) against nearcore: every contract call of every chunk in a
`near-d3-ttn --trace` file is replayed by the Lean spec (`nearspec-v3-wasm --chunk`) against the
witness's recorded pre-state, in nearcore's execution order, and its status, wasm gas, ext gas total
and the 11 per-key storage/trie-node profile slots are compared with nearcore's outcome profile.

  difftest_ttn.py TRACE [--shards K] [--code WASM]   (ttn2.wasm for --v2 traces)

D3_TTN_ABLATE=--ablate-cache / --ablate-overlay runs a deliberately wrong replay (fresh cache per
call / no committed writes between calls) to show the comparison is sensitive.
"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.environ.get("D3_SPEC", os.path.join(HERE, "../wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm"))
SLOTS = ["write_base", "read_base", "read_key_byte", "read_value_byte", "large_read_base",
         "large_read_byte", "remove_base", "has_key_base", "has_key_byte", "touching_trie_node",
         "read_cached_trie_node"]

def main():
    trace = sys.argv[1]
    shards = int(sys.argv[sys.argv.index("--shards") + 1]) if "--shards" in sys.argv else 4
    codef = sys.argv[sys.argv.index("--code") + 1] if "--code" in sys.argv else os.path.join(HERE, "ttn.wasm")
    lines = [l for l in open(trace).read().splitlines() if l.strip()]
    expected = []
    for l in lines:
        t = l.split(" ")
        n = int(t[2]); k = int(t[3 + n]); calls = []
        for j in range(k):
            b = 4 + n + 17 * j
            calls.append((t[b], " ".join(t[b + 3:b + 17])))
        expected.append(calls)
    with tempfile.TemporaryDirectory() as td:
        code = os.path.join(td, "code.hex")
        open(code, "w").write(open(codef, "rb").read().hex())
        procs = []
        for s in range(shards):
            p = os.path.join(td, f"in{s}")
            open(p, "w").write("\n".join(lines[s::shards]) + "\n")
            procs.append(subprocess.Popen([LEAN, "--chunk", code] + os.environ.get("D3_TTN_ABLATE", "").split(), stdin=open(p), stdout=open(p + ".out", "w")))
        for pr in procs:
            pr.wait()
        outs = [open(os.path.join(td, f"in{s}.out")).read().splitlines() for s in range(shards)]
    got = [None] * len(lines)
    for s in range(shards):
        pos = 0
        for ci in range(s, len(lines), shards):
            k = len(expected[ci])
            got[ci] = outs[s][pos:pos + k]
            pos += k
    calls = bad = ttn = fails = 0
    slot_hits = [0] * 11
    kinds = {}
    accts = set()
    for ci, (exp, g) in enumerate(zip(expected, got)):
        for j, (acct, e) in enumerate(exp):
            calls += 1
            accts.add(acct)
            a = g[j] if g and j < len(g) else "<missing>"
            ev = e.split(" ")
            if ev[0].startswith("fail"):
                fails += 1
                kinds[ev[0]] = kinds.get(ev[0], 0) + 1
            for i in range(11):
                if int(ev[3 + i]) > 0:
                    slot_hits[i] += 1
            if int(ev[12]) + int(ev[13]) > 0:
                ttn += 1
            if a != e:
                bad += 1
                if bad <= 10:
                    print(f"DISAGREE chunk {ci} call {j} ({acct})\n  nearcore: {e}\n  spec    : {a}")
    print(f"chunks={len(lines)} calls={calls} failed_calls={fails} calls_with_trie_node_charges={ttn} "
          f"disagreements={bad}")
    print("failure kinds: " + ", ".join(f"{k}={v}" for k, v in sorted(kinds.items())) + f"; contracts={len(accts)}")
    print("calls with nonzero slot: " + ", ".join(f"{n}={c}" for n, c in zip(SLOTS, slot_hits)))
    sys.exit(1 if bad else 0)

main()
