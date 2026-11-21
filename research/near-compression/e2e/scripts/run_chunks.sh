#!/usr/bin/env bash
# Run the delivered D0a pipeline (witness -> base -> L1..L5 -> final -> fresh-process verify -> negatives)
# on each corpus case, sequentially. usage: run_chunks.sh RUNS_DIR CASE_DIR...
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-16} HEAVY_MEM=${HEAVY_MEM:-32G}
RUNS=${1:?runs dir}; shift
mkdir -p "$RUNS"
fail=0
for c in "$@"; do
  n=$(basename "$(dirname "$c")")_$(basename "$c")
  echo "START $n $(date -Is)"
  s=$(date +%s); rc=0
  "$ROOT/research/near-compression/native/pq-chunk-e2e/run.sh" "$RUNS/$n" "$c" > "$RUNS/$n.log" 2>&1 || rc=$?
  echo "END $n rc=$rc wall_s=$(( $(date +%s) - s )) $(date -Is)"
  [ $rc = 0 ] || fail=1
done
[ $fail = 0 ]
