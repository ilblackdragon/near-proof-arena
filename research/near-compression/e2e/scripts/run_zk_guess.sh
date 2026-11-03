#!/usr/bin/env bash
# E2E-D D-2 hiding tests on FINAL proofs (no proving; <= 10 threads):
#   witness-guessing distinguisher: for each packet P and candidate witness W (the FINAL trace
#   generated from W's L4 checkpoint), count the column openings of P that equal W's trace MLEs at
#   P's batch point (NEARPROOF_ZK_GUESS, `zk_guess` in pq-chunk-e2e/src/main.rs).
#   Two-witness test: P against its own chunk's witness and against another chunk's witness.
# usage: run_zk_guess.sh PACKET_DIR... (each with FINAL.proof, SETUP.json)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10}
for P in "$@"; do
  for W in ${WITNESSES:-d1_00-h10006-s3 d1_00-h10007-s0}; do
    S=$D/e2e/$W
    NEARPROOF_ZK_GUESS="$P" taskset -c 8-15,24-25 "$B" replay-final "$AIR" "$S/public" "$S" \
      "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" 4 2>&1 | grep -h "ZK_GUESS" | sed "s|$| witness=$W|"
  done
done
