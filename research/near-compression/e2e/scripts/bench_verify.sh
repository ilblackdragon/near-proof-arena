#!/usr/bin/env bash
# Stage split of the verifier (median of REPS) at 1 and 16 threads, then the full CLI.
# usage: bench_verify.sh RUN_DIR CASE_DIR [REPS] [BINARY]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
R=${1:?run}; CASE=${2:?case}; REPS=${3:-5}
B=${4:-$D/target/release/nearproof-chunk-e2e}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
for t in 1 16; do
  cpus=$([ "$t" = 1 ] && echo 15 || echo 8-15,24-31)
  RAYON_NUM_THREADS=$t taskset -c "$cpus" "$B" verify-bench "$AIR" "$R/public" "$R/SETUP.json" "$R/FINAL.bundle" "$REPS" 2>&1 | grep VERIFY_BENCH
  for i in 1 2 3; do
    s=$(date +%s.%N)
    RAYON_NUM_THREADS=$t taskset -c "$cpus" "$B" verify "$AIR" "$CASE/claim.bin" "$D/target-classical/release/examples/statepublic" \
      "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/FINAL.bundle" 2>&1 | grep -E "VERIFY_PROFILE|INDEPENDENT" | tr '\n' ' '
    echo "threads=$t cli_wall_ms=$(echo "($(date +%s.%N) - $s)*1000" | bc)"
  done
done
