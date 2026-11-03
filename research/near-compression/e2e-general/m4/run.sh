#!/usr/bin/env bash
# E2E M4: a long Wasm call cut into segments, proved segment by segment and chained by hand.
#
#   run.sh <work_dir> [steps_per_segment]
#
# Needs: wasm-base-lean built (`lake build wasmbase-tool`) and the prover built
# (`cd ../../native/wasm-base && cargo build --release`, or WASMBASE_BIN).  Run it inside a
# memory-capped scope on the shared host, e.g.
#   systemd-run --user --scope -p MemoryMax=24G -p MemorySwapMax=0 taskset -c 0-7 ./run.sh W
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?work dir}; K=${2:-262144}
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=${WASMBASE_BIN:-$HERE/../../native/wasm-base/target/release/nearproof-wasm-base}
mkdir -p "$W"; cd "$W"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
# 1. the benchmark call (24,000 iterations: 1,128,011 Wasm steps) and its spec run
python3 "$HERE/gen_bench.py" segbench.wasm 24000
"$TOOL" prepM2 segbench.wasm main 1000000000000000 > segbench.prep.json
"$TOOL" airSeg 0 0 > airSeg.json
"$TOOL" airM2 2 1 > airM2-2-1.json
# 2. check, prove and chain every segment (one verifying key)
SEG_TABLES=1 "$BIN" segcheck airSeg.json airM2-2-1.json segbench.prep.json "$K" > segcheck-bench.log 2>&1
SEG_TABLES=1 "$BIN" segprove airSeg.json airM2-2-1.json segbench.prep.json "$K" > segprove-bench.log 2>&1
# 3. tamper battery on a short corpus call (3b1ad423.run with a register refill; 96 steps, cut
#    every 30 steps): segment 0 (a written block) and segment 2 (read-only block, drops, tombs)
if [ -n "${REFILL_PREP:-}" ]; then
  "$TOOL" airM2 5 1 > airM2-5-1.json
  for s in 0 2; do
    "$BIN" segtamper airSeg.json airM2-5-1.json "$REFILL_PREP" 30 "$s" > "segtamper-refill-s$s.log" 2>&1
  done
fi
