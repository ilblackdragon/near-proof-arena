#!/usr/bin/env bash
# E2E M4 re-validation on the final AIR (after the CUT padding `gl` range fix):
# segcheck of the 1.13 M-step benchmark (all 5 segments), segprove of the refill corpus call
# (4 segments), and segprove of the benchmark's last segment.
#   recheck.sh <work_dir> <bench_prep.json> <refill_prep.json>
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
W=${1:?}; BENCH=${2:?}; REFILL=${3:?}
TOOL=$HERE/../../wasm-base-lean/.lake/build/bin/wasmbase-tool
BIN=${WASMBASE_BIN:-$HERE/../../native/wasm-base/target/release/nearproof-wasm-base}
mkdir -p "$W"; cd "$W"
# the segment AIR: `airSegMP` (wasmBaseSegAirMP, the default since M4c: `seg_sound_mp`) or `airSeg` (M4)
"$TOOL" "${SEG_AIR:-airSegMP}" 0 0 > airSeg.json
"$TOOL" airM2 2 1 > airM2-2-1.json
"$TOOL" airM2 5 1 > airM2-5-1.json
"$BIN" segcheck airSeg.json airM2-2-1.json "$BENCH" 262144 > segcheck-bench.log 2>&1
"$BIN" segprove airSeg.json airM2-5-1.json "$REFILL" 30 > segprove-refill.log 2>&1
SEG_ONLY=4 "$BIN" segprove airSeg.json airM2-2-1.json "$BENCH" 262144 > segprove-bench-s4.log 2>&1
