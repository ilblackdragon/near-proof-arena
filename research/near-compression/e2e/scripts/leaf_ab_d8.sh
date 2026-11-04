#!/usr/bin/env bash
# E2E-D D-8 (leaf cost): the template leaf alone (NEARPROOF_TREE_LEAF_ONLY) over one base proof, at
# several leaf proof geometries (NEARPROOF_TREE_LEAF_PARAMS) and base rates (NEARPROOF_BASE_LB, base
# re-proved), same threads, so leaf seconds / cells / pins compare directly. Fails on any error.
# usage: leaf_ab_d8.sh OUT BASE_DIR LEAF_PARAMS...   (LEAF_PARAMS: "tree" = the tree geometry, or nsXXlbY)
#   env: CPUSET (default 16-17), RAYON_NUM_THREADS (default 2), LEAF_SHA (leaf SHA instances)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
OUT=$1; BASE=$2; shift 2
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-2} NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export NEARPROOF_TREE_GEOM=ns20lb5 NEARPROOF_TREE_LEAF_ONLY=1 NEARPROOF_TREE_LEAF_SHA=${LEAF_SHA:-1}
for g in "$@"; do
  R=$OUT/leaf-$g; rm -rf "$R"; mkdir -p "$R"
  E=(); [ "$g" != tree ] && E=(NEARPROOF_TREE_LEAF_PARAMS="$g")
  env "${E[@]}" taskset -c "${CPUSET:-16-17}" /usr/bin/time -v "$B" tree-prove "$AIR" "$BASE/public" "$R" "$BASE" \
    "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" 4 1 "$BASE" > "$R/prove.log" 2>&1 \
    || { echo "LEAF_AB_FAILED $g $(grep -h -A2 panicked "$R/prove.log" | head -3 | tr '\n' ' ')"; exit 1; }
  grep -q TREE_LEAF_ONLY_DONE "$R/prove.log" || { echo "LEAF_AB_FAILED $g: no TREE_LEAF_ONLY_DONE"; exit 1; }
  echo "LEAF_AB $g $(grep -h 'TREE_LEAF_PARAMS\|TREE_TEMPLATE \|TREE_LEAF 0\|TREE_LEAF_ONLY_DONE\|Maximum resident' "$R/prove.log" | tr '\n' ' ')"
done
echo LEAF_AB_DONE
