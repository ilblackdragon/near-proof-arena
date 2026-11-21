#!/usr/bin/env bash
# E2E-D M8 regression: the M8 circuit change leaves the D0a tree unchanged. With the D-9 production
# setup fixed (NEARPROOF_TREE_SETUP) and NEARPROOF_TREE_TEMPLATES_ONLY=1, `tree-prove` rebuilds every
# class's base key (class_key_check) and every class's leaf program at its family geometry, and
# requires the template entries (incl. each class's leaf program root C_t) and every family's
# PAD_L root to equal the setup's: TREE_TEMPLATES_MATCH_FIXED_SETUP.
#   usage: regress_m8_d9.sh OUT
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
O=${1:?out}; mkdir -p "$O"
B=${PROVER:-/data/illia/nearproof-deps/pq-e2e-m8/drv2/release/nearproof-chunk-e2e}
D9=/data/illia/nearproof-deps/pq-e2e-d9
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
CH=$D9/b8/d1_10-h10075-s0
CLASS_DIRS="$D9/b8/d1_10-h10075-s0 $D9/b8/d1_10-h10056-s2 $D9/b8/d1_01-h10040-s3"
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6 NEARPROOF_TREE_GEOM=ns20lb5
export NEARPROOF_TREE_LEAF_PARAMS=ns20lb2 NEARPROOF_TREE_LEAF_FAMILIES=auto
export NEARPROOF_TREE_SETUP=$D9/tree9/d1_10-h10075-s0/SETUP.json NEARPROOF_TREE_TEMPLATES_ONLY=1
# shellcheck disable=SC2086
RAYON_NUM_THREADS=${THREADS:-2} taskset -c "${CPUSET:-8-9}" "$B" tree-prove "$AIR" "$CH/public" "$O/run" "$CH" \
  "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" 4 1 $CLASS_DIRS > "$O/regress.log" 2>&1 \
  || { grep -h -A3 panicked "$O/regress.log" | head -5; exit 1; }
grep -hE "TREE_CLASS_KEY_REBUILT|TREE_TEMPLATES_MATCH_FIXED_SETUP" "$O/regress.log"
grep -q TREE_TEMPLATES_MATCH_FIXED_SETUP "$O/regress.log"
echo M8_D9_REGRESSION_OK
