#!/bin/sh
# Exact-limit cases (plans calibrated by the clean-room agent with --deltas): re-generate the
# traces and difftest the Lean spec. Usage: runs/limit/run.sh (from oracle/d3-ttn)
set -e
H="taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy"
T=${TMPDIR:-/tmp}
for p in final final2 final3; do
  RUST_LOG=error $H ./target/debug/near-d3-ttn --v2 --seed 7 --blocks 22 --ops 60 \
    --limit-plan runs/limit/plan-$p.txt --out $T/lim-$p.json --trace $T/lim-$p.trace > runs/limit/$p.summary 2>/dev/null
  $H python3 difftest_ttn.py $T/lim-$p.trace --shards 8 --code ttn2.wasm > runs/limit/$p.difftest
  printf '%s\n' "$(cat ttn2.wasm | od -An -tx1 -v | tr -d ' \n')" > $T/lim-code.hex
  $H ../wasm-d3/lean/.lake/build/bin/nearspec-v3-wasm --chunk $T/lim-code.hex --deltas < $T/lim-$p.trace > $T/lim-$p.lean
  python3 - "$T/lim-$p.trace" "$T/lim-$p.lean" runs/limit/plan-$p.txt > runs/limit/$p.limits <<'PY'
import sys
tr, le, pl = sys.argv[1:]
plan = {(l.split()[1], l.split()[2]) for l in open(pl) if l.strip()}
lean = open(le).read().splitlines(); li = 0
for ci, line in enumerate(open(tr)):
    t = line.split(); n = int(t[2]); k = int(t[3 + n])
    for j in range(k):
        b = 4 + n + 17 * j; got = lean[li]; li += 1
        if (t[b], t[b + 2]) in plan:
            print(f"chunk {ci} {t[b]} growth {got.split(' d=')[1]} nearcore {t[b+3]} spec {got.split()[0]}")
PY
  rm -f $T/lim-$p.trace $T/lim-$p.json $T/lim-$p.lean
done
