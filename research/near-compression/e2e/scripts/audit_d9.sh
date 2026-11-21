#!/usr/bin/env bash
# E2E-D D-9 (review-D7 L3, review-D8 M1 / M2 / L1): audit a tree setup against the declared AIR and
# its shipped class base vks: every class key rebuilt from AIR + TAPE pad + the calibration for its
# shape (byte for byte), then (setup version 6) every family's PAD_L root, the leaf roots
# regenerated from base proofs (every class covered), C_padN, and, over the run's own leaves and
# root, C_2 of its family, the wrap program, its pinned heights and the final vk. Exit 1 on a
# mismatch (an audit that finds nothing to check fails too).
# usage: audit_d9.sh RUN_DIR BASE_DIR...   -> RUN_DIR/audit.txt   (env SETUP: another SETUP.json)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
R=$1; shift
export NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_ZK_FINAL=6 RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-2}
rc=0
taskset -c "${CPUSET:-24-25}" "$B" tree-audit "$AIR" "${SETUP:-$R/SETUP.json}" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$R" "$@" > "$R/audit.log" 2>&1 || rc=$?
grep -h "TREE_AUDIT" "$R/audit.log" | tee "$R/audit.txt"
[ "$rc" = 0 ] && grep -q TREE_AUDIT_OK "$R/audit.txt" || { echo "AUDIT_FAILED rc=$rc"; exit 1; }
