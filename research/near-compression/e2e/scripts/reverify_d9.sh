#!/usr/bin/env bash
# E2E-D D-9: re-time fresh-process verification of tree runs (3x each, 1 thread, one CPU), e.g. when
# the run's own verify ran on a loaded host. Writes RUN_DIR/reverify.txt; fails on any rejection.
# usage: reverify_d9.sh BASE_ROOT RUN_DIR...   (claim = BASE_ROOT/<run name>/claim.bin; env VERIFY_CPU, default 24)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
BR=$1; shift
for R in "$@"; do
  n=$(basename "$R"); : > "$R/reverify.txt"
  echo "LOAD $(cut -d' ' -f1-3 /proc/loadavg)" >> "$R/reverify.txt"
  for i in 1 2 3; do
    RAYON_NUM_THREADS=1 taskset -c "${VERIFY_CPU:-24}" "$B" tree-verify "$AIR" "$BR/$n/claim.bin" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/WRAP.bundle" \
      | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK" >> "$R/reverify.txt"
  done
  [ "$(grep -c INDEPENDENT_TREE_VERIFY_OK "$R/reverify.txt")" = 3 ] || { echo "REVERIFY_FAILED $R"; exit 1; }
  echo "REVERIFY $n $(grep -o 'total=[0-9.]* wrap_verify=[0-9.]*' "$R/reverify.txt" | tr '\n' ' ')"
done
