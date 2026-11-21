#!/usr/bin/env bash
# E2E-D D-9 (leaf families): the template leaf alone (NEARPROOF_TREE_LEAF_ONLY) of one chunk over the
# production class dirs (S1 M1 L1), proved twice back to back at equal threads:
#   one  = NEARPROOF_TREE_LEAF_FAMILIES=one at NvAir 2^20 / program 2^19 (D-8: L's leaf sets every
#          leaf's heights)
#   auto = the chunk's own family (D-9)
# so the leaf seconds / bytes / heights compare directly. Fails on any error.
# usage: leaf_family_ab_d9.sh OUT CHUNK_BASE_DIR CLASS_DIR...   (env CPUSET default 24-25, 2 threads)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d9}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
OUT=$1; CH=$2; shift 2
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-2} NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export NEARPROOF_TREE_GEOM=ns20lb5 NEARPROOF_TREE_LEAF_ONLY=1 NEARPROOF_TREE_LEAF_PARAMS=ns20lb2
for m in one auto; do
  R=$OUT/leaf-$m; rm -rf "$R"; mkdir -p "$R"
  NEARPROOF_TREE_LEAF_FAMILIES=$m NEARPROOF_TREE_LEAF_GEOM=20,19 taskset -c "${CPUSET:-24-25}" /usr/bin/time -v "$B" tree-prove "$AIR" "$CH/public" "$R" "$CH" \
    "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" - 1 "$@" > "$R/prove.log" 2>&1 \
    || { echo "LEAF_FAMILY_AB_FAILED $m $(grep -h -A2 panicked "$R/prove.log" | head -3 | tr '\n' ' ')"; exit 1; }
  grep -q TREE_LEAF_ONLY_DONE "$R/prove.log" || { echo "LEAF_FAMILY_AB_FAILED $m: no TREE_LEAF_ONLY_DONE"; exit 1; }
  echo "LEAF_FAMILY_AB $m $(grep -h 'TREE_LEAF_FAMILIES\|TREE_LEAF 0\|TREE_LEAF_ONLY_DONE\|Maximum resident\|Elapsed' "$R/prove.log" | tr '\n' ' ')"
done
echo LEAF_FAMILY_AB_DONE
