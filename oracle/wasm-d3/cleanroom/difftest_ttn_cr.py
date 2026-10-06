#!/usr/bin/env python3
"""Op-level difftest of the clean-room trie-backed storage (nearstore.py, checkpoint 3b) against nearcore.

Every contract call of every chunk of a `near-d3-ttn --trace` file (docs/research/d3-trie-accounting.md
section 5) is replayed by `nearwasm.py --chunk` against the recorded pre-state, in outcome order, and its
status, wasm gas, ext gas total and the 11 storage/trie-node profile slots are compared with nearcore's
outcome profile.

  difftest_ttn_cr.py TRACE [--shards K] [--code WASM]   (default oracle/d3-ttn/ttn.wasm; ttn2.wasm for --v2)

The status column is `ok` or `fail:KIND` (KIND = HostError variant name, section 5).

Exit status 1 on any disagreement.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
WASM = os.path.join(HERE, "../../d3-ttn/ttn.wasm")
SLOTS = ["write_base", "read_base", "read_key_byte", "read_value_byte", "large_read_base",
         "large_read_byte", "remove_base", "has_key_base", "has_key_byte", "touching_trie_node",
         "read_cached_trie_node"]


def main():
    trace = sys.argv[1]
    shards = int(sys.argv[sys.argv.index("--shards") + 1]) if "--shards" in sys.argv else 4
    codef = sys.argv[sys.argv.index("--code") + 1] if "--code" in sys.argv else WASM
    lines = [l for l in open(trace).read().splitlines() if l.strip()]
    expected = []
    for l in lines:
        t = l.split(" ")
        n = int(t[2])
        k = int(t[3 + n])
        calls = []
        for j in range(k):
            b = 4 + n + 17 * j
            calls.append((t[b], " ".join(t[b + 3:b + 17])))
        expected.append(calls)
    shards = max(1, min(shards, len(lines)))
    with tempfile.TemporaryDirectory() as td:
        code = os.path.join(td, "code.hex")
        with open(code, "w") as f:
            f.write(open(codef, "rb").read().hex())
        procs = []
        for s in range(shards):
            p = os.path.join(td, f"in{s}")
            with open(p, "w") as f:
                f.write("\n".join(lines[s::shards]) + "\n")
            procs.append(subprocess.Popen([sys.executable, os.path.join(HERE, "nearwasm.py"), "--chunk", code],
                                          stdin=open(p), stdout=open(p + ".out", "w")))
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
    calls = bad = fails = ttn = 0
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
                    print(f"DISAGREE chunk {ci} call {j} ({acct})\n  nearcore  : {e}\n  cleanroom : {a}")
    print(f"chunks={len(lines)} calls={calls} failed_calls={fails} calls_with_trie_node_charges={ttn} "
          f"disagreements={bad}")
    print("failure kinds: " + ", ".join(f"{k}={v}" for k, v in sorted(kinds.items())) + f"; contracts={len(accts)}")
    print("calls with nonzero slot: " + ", ".join(f"{n}={c}" for n, c in zip(SLOTS, slot_hits)))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
