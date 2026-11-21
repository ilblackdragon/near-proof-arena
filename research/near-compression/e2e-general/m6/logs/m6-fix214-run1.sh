#!/usr/bin/env bash
# FIX214: export AIRs, d3tiny segcheck (before/after), refill segcheck/segprove/segtamper on MP, bench recheck
set -u
D=/data/illia/nearproof-deps/e2e-laneA/m6-fix214
W=/data/illia/nearproof/.claude/worktrees/agent-a6e1273c00a91e677/research/near-compression
TOOL=$W/wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=$D/nearproof-wasm-base
REFILL=/data/illia/nearproof-deps/e2e-laneA/m2mut/refill.json
TINY=/data/illia/nearproof-deps/e2e-laneA/m6-grow/sweep/preps/000009.json
export RAYON_NUM_THREADS=8
cd $D
"$TOOL" airSegMP 0 0 > airSegMP.json
"$TOOL" airSeg 0 0 > airSeg.json
"$TOOL" airSegG 0 0 > airSegG.json
"$TOOL" airM2 5 1 > airM2-5-1.json
"$TOOL" airM2 2 1 > airM2-2-1.json
"$TOOL" airM2 1 0 > airM2-1-0.json
sha256sum airSegMP.json airSeg.json airSegG.json airM2-1-0.json airM2-5-1.json airM2-2-1.json $TINY $REFILL > inputs.sha256
SEG_CONTINUE=1 "$BIN" segcheck airSegMP-old.json airM2-1-0.json $TINY 8 > segcheck-d3tiny-mp-before.log 2>&1
echo "d3tiny before exit $?"; grep -E "PRECHECK|SEGCHECK" segcheck-d3tiny-mp-before.log
for a in airSegMP airSeg; do
  SEG_CONTINUE=1 "$BIN" segcheck $a.json airM2-1-0.json $TINY 8 > segcheck-d3tiny-$a.log 2>&1
  echo "d3tiny $a exit $?"; grep -E "PRECHECK|SEGCHECK" segcheck-d3tiny-$a.log
done
SEG_ONLY=2 "$BIN" segprove airSegMP.json airM2-1-0.json $TINY 8 > segprove-d3tiny-mp-s2.log 2>&1
echo "d3tiny prove s2 exit $?"; tail -8 segprove-d3tiny-mp-s2.log
"$BIN" segtamper airSegMP.json airM2-1-0.json $TINY 8 2 > segtamper-d3tiny-mp-s2.log 2>&1
echo "d3tiny tamper s2 exit $?"; tail -4 segtamper-d3tiny-mp-s2.log
for a in airSegMP airSeg; do
  SEG_TABLES=1 "$BIN" segcheck $a.json airM2-5-1.json "$REFILL" 30 > segcheck-refill-$a.log 2>&1
  echo "refill $a exit $?"; tail -2 segcheck-refill-$a.log
  for s in 0 2; do
    "$BIN" segtamper $a.json airM2-5-1.json "$REFILL" 30 $s > segtamper-refill-$a-s$s.log 2>&1
    echo "tamper refill $a s$s exit $?"; tail -3 segtamper-refill-$a-s$s.log
  done
done
"$BIN" segprove airSegMP.json airM2-5-1.json "$REFILL" 30 > segprove-refill-mp.log 2>&1
echo "refill prove exit $?"; tail -4 segprove-refill-mp.log
echo RUN1 DONE
