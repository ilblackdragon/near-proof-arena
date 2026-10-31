#!/usr/bin/env bash
# Witness-generate candidate corpus cases under the D0a AIR; a case is D0a-provable iff statedump succeeds.
# usage: scan_d0a.sh OUTDIR CASE_DIR...
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
OUT=${1:?outdir}; shift
mkdir -p "$OUT"
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
for c in "$@"; do
  n=$(basename "$(dirname "$c")")_$(basename "$c")
  start=$(date +%s.%N)
  "$D/target-classical/release/examples/statedump" d0a "$AIR" "$c" "$OUT/$n" > "$OUT/$n.log" 2>&1
  rc=$?
  end=$(date +%s.%N)
  echo "$c rc=$rc secs=$(echo "$end - $start" | bc) :: $(tail -1 "$OUT/$n.log")"
done
