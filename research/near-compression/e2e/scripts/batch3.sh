#!/usr/bin/env bash
# The three corpus chunks of the e2e runs, sequentially. 2026-11-03 (E2E-D, ZK lever on): fresh
# witness and base for every chunk (the base commits with zk = 1, so a reused 10-31 base would
# not do), at most 10 threads on CPUs 8-15,24-25.
# usage: batch3.sh [OUT_ROOT] [SRC_ROOT_TO_REUSE_BASES]
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=${1:-/data/illia/nearproof-deps/pq-e2e-d/e2e}
OLD=${2:-}
C=/data/illia/nearproof-deps/corpora
export NEARPROOF_ZK=${NEARPROOF_ZK:-1} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10} CPUSET=${CPUSET:-8-15,24-25}
mkdir -p "$R"
one() {
  local name=$1 case=$2
  local src=""; [ -n "$OLD" ] && src="$OLD/$name"
  echo "START $name $(date -Is)"
  local s; s=$(date +%s)
  bash "$HERE/e2e_case.sh" "$R/$name" "$case" $src > "$R/$name.log" 2>&1
  echo "END $name rc=$? wall_s=$(( $(date +%s) - s )) $(date -Is)"
}
one d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3"
one d1_00-h10007-s0 "$C/d1run/d1/00-h10007-s0"
one d2_05-h10042-s3 "$C/d2corpus.v2/d2/05-h10042-s3"
