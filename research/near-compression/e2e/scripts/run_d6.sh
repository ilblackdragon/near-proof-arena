#!/usr/bin/env bash
# E2E-D milestone D-6 (2026-11-04): the tree wrap over shape-floored template classes.
#  1. arity 2, depth 1 on all three D0a chunks with ONE setup (chunk 1 creates it; chunks 2, 3 are
#     proved against it and must reproduce it byte for byte), fresh-process negatives per chunk;
#  2. the template set rebuilt from a FRESH chain of chunk 1 (other base u, other transcripts) must
#     equal the setup's (NEARPROOF_TREE_TEMPLATES_ONLY);
#  3. arity 2, depth 2 (4 leaves: the template leaf + 3 PAD; 2 + 1 nodes) on chunks 2 and 3, one setup;
#  4. the arity probe over the depth-2 run's leaves: node trace shapes at arity 2, 3, 4, 8, and a
#     proved 3-ary node.
#  5. (prototype) the base-template tree: leaves verify the class base proof directly
#     (NEARPROOF_TREE_TEMPLATE=base, nv/tree.rs build_base_leaf), BASE_CHUNKS (default chunk 1).
# Classes: run_shape_classes.sh output (CLASS_ROOT). Sequential, <= 10 threads, <= 40 GB.
# usage: run_d6.sh [STEPS]   (default "1 2 3 4")
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d6}
export PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
CL=${CLASS_ROOT:-$D/classes}
CLB=${CLASS_ROOT_B:-$D/classesB}
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
C1=d1_00-h10006-s3; C2=d1_00-h10007-s0; C3=d2_05-h10042-s3
declare -A CLAIM=(
  [$C1]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3/claim.bin
  [$C2]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10007-s0/claim.bin
  [$C3]=/data/illia/nearproof-deps/corpora/d2corpus.v2/d2/05-h10042-s3/claim.bin
)
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10} HEAVY_MEM=${HEAVY_MEM:-40G} CPUSET=${CPUSET:-8-15,24-25}
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
STEPS=${1:-1 2 3 4}
negs() { # TAG CHUNK OTHER_CHUNK
  python3 "$HERE/tree_negatives.py" "$D/$1/$2" "${CLAIM[$2]}" "${CLAIM[$3]}" "$D/$1/$3" > "$D/$1/$2/negatives.txt" 2>&1
  tail -1 "$D/$1/$2/negatives.txt"
}
for s in $STEPS; do case $s in
1)
  echo "== step 1: tree-a2d1 on $C1 $C2 $C3 (one setup)"
  CLASS_ROOT=$CL OUT_ROOT=$D TAG=tree-a2d1 CHUNKS="$C1 $C2 $C3" NEARPROOF_PQ_DEPS=$D "$HERE/run_tree.sh" 2 1
  for c in $C2 $C3; do cmp "$D/tree-a2d1/$C1/SETUP.json" "$D/tree-a2d1/$c/SETUP.json" && echo "SETUP_IDENTICAL $C1 $c"; done
  negs tree-a2d1 $C1 $C2; negs tree-a2d1 $C2 $C3; negs tree-a2d1 $C3 $C1
  ;;
2)
  echo "== step 2: template set from a fresh chain of $C1 against the step-1 setup"
  mkdir -p "$CLB"; for c in $C2 $C3; do ln -sfn "$CL/$c" "$CLB/$c"; done
  X=$D/tree-fresh-templates; rm -rf "$X"; mkdir -p "$X"
  NEARPROOF_TREE_SETUP=$D/tree-a2d1/$C1/SETUP.json NEARPROOF_TREE_TEMPLATES_ONLY=1 \
    taskset -c "$CPUSET" /data/illia/nearproof-deps/bin/heavy "$PROVER" tree-prove "$AIR" "$CLB/$C1/public" "$X" "$CLB/$C1" \
    "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" 2 1 "$CLB/$C1" "$CLB/$C2" "$CLB/$C3" > "$X/prove.log" 2>&1
  echo "FRESH_TEMPLATES rc=$? $(grep -h 'TREE_TEMPLATES_MATCH_FIXED_SETUP\|panicked' "$X/prove.log")"
  cmp -s "$CL/$C1/L4.proof" "$CLB/$C1/L4.proof" && echo "WARNING: same L4" || echo "FRESH_L4 (the fresh chain's L4 differs)"
  ;;
3)
  echo "== step 3: tree-a2d2 on $C2 $C3 (one setup)"
  CLASS_ROOT=$CL OUT_ROOT=$D TAG=tree-a2d2 CHUNKS="$C2 $C3" NEARPROOF_PQ_DEPS=$D "$HERE/run_tree.sh" 2 2
  cmp "$D/tree-a2d2/$C2/SETUP.json" "$D/tree-a2d2/$C3/SETUP.json" && echo "SETUP_IDENTICAL $C2 $C3"
  negs tree-a2d2 $C2 $C3; negs tree-a2d2 $C3 $C2
  ;;
4)
  echo "== step 4: arity probe over the depth-2 leaves of $C2"
  R=$D/tree-a2d2/$C2
  taskset -c "$CPUSET" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v "$PROVER" tree-arity \
    "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$R" 2,3,4,8 "${PROVE_ARITY:-3}" "$CL/$C1" "$CL/$C2" "$CL/$C3" > "$R/arity.log" 2>&1
  echo "ARITY rc=$?"; grep -h "TREE_ARITY\|Maximum resident\|panicked" "$R/arity.log" | cut -c1-600
  ;;
5)
  echo "== step 5: base-template tree (the leaf verifies the class base proof directly: lane A/B leaf prototype), arity 2, depth 1"
  NEARPROOF_TREE_TEMPLATE=base CLASS_ROOT=$CL OUT_ROOT=$D TAG=tree-base-a2d1 CHUNKS="${BASE_CHUNKS:-$C1}" NEARPROOF_PQ_DEPS=$D "$HERE/run_tree.sh" 2 1
  for c in ${BASE_CHUNKS:-$C1}; do negs tree-base-a2d1 "$c" "$C2"; done
  ;;
esac; done
echo D6_DONE
