#!/usr/bin/env bash
# E2E-D D-6: fresh-process tree-verify timing (1 thread, 1 core, 5 runs per packet) of every D-6
# tree packet, with nothing else of this lane running.
# usage: bench_tree_verify.sh [DEPS]
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${1:-/data/illia/nearproof-deps/pq-e2e-d6}
B=${PROVER:-$D/bin/prover-d6b}
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
declare -A CLAIM=(
  [d1_00-h10006-s3]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3/claim.bin
  [d1_00-h10007-s0]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10007-s0/claim.bin
  [d2_05-h10042-s3]=/data/illia/nearproof-deps/corpora/d2corpus.v2/d2/05-h10042-s3/claim.bin
)
for R in "$D"/tree-a2d1/* "$D"/tree-a2d2/* "$D"/tree-base-a2d1/*; do
  [ -f "$R/WRAP.bundle" ] || continue
  c=$(basename "$R")
  for i in 1 2 3 4 5; do
    RAYON_NUM_THREADS=1 taskset -c "${CORE:-9}" "$B" tree-verify "$AIR" "${CLAIM[$c]}" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/WRAP.bundle" 2>&1 \
      | grep -h "VERIFY_PROFILE_MS\|panicked" | sed "s|^|$(basename "$(dirname "$R")")/$c |"
  done
done
