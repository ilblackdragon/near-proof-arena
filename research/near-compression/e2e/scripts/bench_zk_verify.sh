#!/usr/bin/env bash
# Collect the three ZK-lever runs and time the fresh-process verifier on one core (5 runs each).
# usage: bench_zk_verify.sh [E2E_ROOT] [CPU]
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
E=${1:-/data/illia/nearproof-deps/pq-e2e-d/e2e}; CPU=${2:-30}
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
OUT=$HERE/../results/zk
for r in d1_00-h10006-s3 d1_00-h10007-s0 d2_05-h10042-s3; do
  python3 "$HERE/collect.py" "$E/$r" "$OUT" > /dev/null
  for i in 1 2 3 4 5; do
    "$HERE/time_verify.sh" "$E/$r" 1 "$CPU" 2>&1 | grep -oE "VERIFY_PROFILE_MS.*|wall_s=[0-9.]+ max_rss_kb=[0-9]+" | tr '\n' ' '
    echo " run=$r"
  done
done | tee "$OUT/verify-1thread.txt"
uptime | tee -a "$OUT/verify-1thread.txt"
