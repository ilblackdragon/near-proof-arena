#!/usr/bin/env bash
# Prove FINAL and INIT for one dump without rebuilding (the Lean tool and prover must be built).
#   prove_both.sh DUMP_JSON OUT_DIR
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DUMP=$1; OUT=$2
TOOL=$HERE/lean/.lake/build/bin/m5d-tool
BIN=${TARGET_DIR:-/data/illia/nearproof-deps/e2e-m5d/target}/release/nearproof-e2e-m5d
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-40G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$OUT"
for T in final init; do
  "$TOOL" "air-$T" "$OUT/$T.json" "$OUT/$T-names.json" > /dev/null
  python3 "$HERE/tracegen.py" "$DUMP" "$OUT/$T-names.json" "$OUT/dump-$T" | tee "$OUT/gen-$T.txt"
  nice -n 10 $HEAVY "$BIN" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/dump-$T" prove | tee "$OUT/$T-prove.log"
done
