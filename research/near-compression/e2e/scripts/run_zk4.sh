#!/usr/bin/env bash
# E2E-D milestone D-2 (2026-11-03): re-prove the FINAL layer of the three D0a chunks with full
# zero-knowledge masking (`NEARPROOF_ZK_FINAL=4`: PCS layer of zk = 2 plus the PIOP masks of
# ZK-ARGUMENT.md §4) from each chunk's existing L4 checkpoint (base zk = 1 and L1..L4 are not
# changed by the FINAL-only masking), then verify every packet in fresh processes.
# usage: run_zk4.sh [TAG] [extra env assignments...]   (sequential, <= 10 threads)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
C=/data/illia/nearproof-deps/corpora
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
TAG=${1:-zk4}; shift || true
declare -A CLAIM=(
  [d1_00-h10006-s3]=$C/d1run/d1/00-h10006-s3/claim.bin
  [d1_00-h10007-s0]=$C/d1run/d1/00-h10007-s0/claim.bin
  [d2_05-h10042-s3]=$C/d2corpus.v2/d2/05-h10042-s3/claim.bin
)
for c in ${CHUNKS:-d1_00-h10006-s3 d1_00-h10007-s0 d2_05-h10042-s3}; do
  S=$D/e2e/$c; R=$D/$TAG/$c
  rm -rf "$R"; mkdir -p "$R"
  cp -r "$S/public" "$S/BASE.proof" "$S/BASE.vk.json" "$S/BASE.u.json" "$S/L4.proof" "$S/L4.vk.json" "$S/L4.state.json" "$S/hint.bin" "$R/"
  echo "LOAD_BEFORE $c $(cut -d' ' -f1-3 /proc/loadavg)"
  env NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=4 "$@" PROVER="$B" "$HERE/replay_final.sh" "$R" 4 "${CLAIM[$c]}" > "$R.out" 2>&1
  echo "REPLAY $c rc=$? $(grep -h FINAL_REPLAY "$R/final.log")"
  grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_VERIFY_OK" "$R/verify.log"
  for i in 1 2 3 4 5; do
    RAYON_NUM_THREADS=1 taskset -c 8 "$B" verify "$(cd "$HERE/../../../.." && pwd)/examples/np-udr-stark-v2/source/near-air-v3.json" \
      "${CLAIM[$c]}" unused "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/FINAL.bundle" 2>&1 | grep -h VERIFY_PROFILE_MS
  done
  echo "LOAD_AFTER $c $(cut -d' ' -f1-3 /proc/loadavg)"
  "$B" soundness "$R/SETUP.json" > "$R/soundness.txt" 2>&1
done
echo ZK4_DONE
