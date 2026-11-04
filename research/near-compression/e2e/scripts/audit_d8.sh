#!/usr/bin/env bash
# E2E-D D-8 (review-D7 L3): audit a tree setup against its shipped class base vks and regenerate
# each class's leaf root from base proofs at the class shapes (tree-audit). Fails on a mismatch.
# usage: audit_d8.sh RUN_DIR BASE_DIR...   -> RUN_DIR/audit.txt
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
R=$1; shift
export NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TREE_GEOM=ns20lb5 RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-2}
taskset -c "${CPUSET:-24-25}" "$B" tree-audit "$R/SETUP.json" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$R" "$@" > "$R/audit.log" 2>&1
rc=$?
grep -h TREE_AUDIT "$R/audit.log" | tee "$R/audit.txt"
[ $rc = 0 ] && grep -q TREE_AUDIT_OK "$R/audit.txt" || { echo "AUDIT_FAILED rc=$rc"; exit 1; }
