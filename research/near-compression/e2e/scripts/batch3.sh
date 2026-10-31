#!/usr/bin/env bash
# The three corpus chunks of the 2026-10-31 e2e run, sequentially (16 threads each).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=${1:-/data/illia/nearproof-deps/pq-e2e-zk/e2e}
C=/data/illia/nearproof-deps/corpora
OLD=/data/illia/nearproof-deps/pq-e2e-zk/runs
mkdir -p "$R"
one() {
  local name=$1 case=$2 src=${3:-}
  echo "START $name $(date -Is)"
  local s; s=$(date +%s)
  bash "$HERE/e2e_case.sh" "$R/$name" "$case" $src > "$R/$name.log" 2>&1
  echo "END $name rc=$? wall_s=$(( $(date +%s) - s )) $(date -Is)"
}
one d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3" "$OLD/d1_00-h10006-s3"
one d1_00-h10007-s0 "$C/d1run/d1/00-h10007-s0" "$OLD/d1_00-h10007-s0"
one d2_05-h10042-s3 "$C/d2corpus.v2/d2/05-h10042-s3"
