#!/usr/bin/env bash
# Fresh-process, single-thread timing of `verify` on the three ZK-lever runs (read-only inputs).
# usage: bench_verify_inprocess.sh BINARY CPU [RUNS] [E2E_ROOT] [LABEL]
# The STATEPUBLIC argument is the run's tools/statepublic (ignored by in-process verifiers).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
B=${1:?binary}; CPU=${2:?cpu}; N=${3:-5}
E=${4:-/data/illia/nearproof-deps/pq-e2e-d/e2e}; LABEL=${5:-}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export RAYON_NUM_THREADS=1
echo "BENCH label=$LABEL binary=$B cpu=$CPU $(uptime)"
for r in d1_00-h10006-s3 d1_00-h10007-s0 d2_05-h10042-s3; do
  R=$E/$r
  CASE=$(python3 -c "import json,sys;d=json.load(open(sys.argv[1]));print([p for p in d['inputs'] if p.endswith('claim.bin')][0].rsplit('/',1)[0])" "$R/RUN.json")
  for i in $(seq 1 "$N"); do
    out=$(/usr/bin/time -f "wall_s=%e max_rss_kb=%M" taskset -c "$CPU" "$B" verify "$AIR" "$CASE/claim.bin" \
      "$R/tools/statepublic" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/FINAL.bundle" 2>&1)
    echo "$(echo "$out" | grep -oE "VERIFY_PROFILE_MS.*|INDEPENDENT_VERIFY_OK|wall_s=[0-9.]+ max_rss_kb=[0-9]+" | tr '\n' ' ') run=$r"
  done
done
echo "BENCH_END $(uptime)"
