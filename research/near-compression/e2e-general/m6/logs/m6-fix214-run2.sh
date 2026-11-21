#!/usr/bin/env bash
# FIX214 run 2: Lean checker on dumped segments (multi-group), bench segcheck, run_grow.sh, grow corpus
set -u
D=/data/illia/nearproof-deps/e2e-laneA/m6-fix214
W=/data/illia/nearproof/.claude/worktrees/agent-a6e1273c00a91e677/research/near-compression
TOOL=$W/wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=$D/nearproof-wasm-base
REFILL=/data/illia/nearproof-deps/e2e-laneA/m2mut/refill.json
TINY=/data/illia/nearproof-deps/e2e-laneA/m6-grow/sweep/preps/000009.json
BENCH=/data/illia/nearproof-deps/e2e-laneA/m4c/tmp-link/bench/segbench.prep.json
export RAYON_NUM_THREADS=8 WASMBASE_BIN=$BIN
mkdir -p $D/nv && cd $D/nv
"$BIN" segdump ../airSegMP.json ../airM2-1-0.json $TINY 8 tinymp > segdump-tinymp.log 2>&1 || echo "SEGDUMP tinymp FAILED"
"$BIN" segdump ../airSeg.json ../airM2-1-0.json $TINY 8 tiny > segdump-tiny.log 2>&1 || echo "SEGDUMP tiny FAILED"
"$BIN" segdump ../airSegMP.json ../airM2-5-1.json $REFILL 30 refmp > segdump-refmp.log 2>&1 || echo "SEGDUMP refmp FAILED"
for i in 0 1 2 3; do
  "$TOOL" holds segMP 0 0 tinymp-$i.bin
  "$TOOL" holds seg 0 0 tiny-$i.bin
  "$TOOL" holds segMP 0 0 refmp-$i.bin
done
cd $D
SEG_TABLES=1 "$BIN" segcheck airSegMP.json airM2-2-1.json $BENCH 262144 > segcheck-bench.log 2>&1
echo "bench segcheck exit $?"; tail -2 segcheck-bench.log
bash $W/e2e-general/m4/run_grow.sh $D/grow 20 500 > rungrow.out 2>&1
echo "run_grow exit $?"
for f in grow/m4c-grow-segcheck.log grow/m4c-grow-segprove.log grow/m4c-grow-segtamper-s1.log grow/m4c-grow-segtamper-s4.log; do echo "== $f"; tail -2 $f; done
echo RUN2 DONE
