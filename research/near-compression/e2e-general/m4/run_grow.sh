#!/usr/bin/env bash
# E2E M4c: segments containing `memory.grow` (`wasmBaseSegAirG`, WasmBase/SegAirG.lean).
#
#   run_grow.sh <work_dir> [n] [steps_per_segment]
#
# growbench(n) (gen_grow.py): grow 1 page mid-call (1024 -> 1025 pages, tree depth 16 -> 17) and
# later 2 pages (depth stays 17), memory.size, a failing grow; traced at `wasmBaseM3Air` (prepM3),
# cut every K steps.  Run inside a memory-capped scope (the prover needs up to ~20 GB on large
# segments), e.g. systemd-run --user --scope -p MemoryMax=24G ./run_grow.sh W
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?work dir}; N=${2:-20}; K=${3:-500}
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=${WASMBASE_BIN:-$HERE/../../native/wasm-base/target/release/nearproof-wasm-base}
mkdir -p "$W"; cd "$W"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8}
python3 "$HERE/gen_grow.py" "grow$N.wasm" "$N"
"$TOOL" prepM3 "grow$N.wasm" main 1000000000000000 > "grow$N.prep.json"
"$TOOL" airSegG 0 0 > airSegG.json
"$TOOL" airM3 2 1 > airM3-2-1.json
SEG_TABLES=1 "$BIN" segcheck airSegG.json airM3-2-1.json "grow$N.prep.json" "$K" > m4c-grow-segcheck.log 2>&1
# with n = 20, K = 500: segment 1 has the lifting grow, segment 4 the second grow
SEG_ONLY=1,4 "$BIN" segprove airSegG.json airM3-2-1.json "grow$N.prep.json" "$K" > m4c-grow-segprove.log 2>&1
for s in 1 4; do
  SEG_TAMPER_G=1 "$BIN" segtamper airSegG.json airM3-2-1.json "grow$N.prep.json" "$K" "$s" > "m4c-grow-segtamper-s$s.log" 2>&1
done
