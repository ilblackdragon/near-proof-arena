#!/usr/bin/env bash
# E2E-D milestone D-7 (2026-11-04): two node shapes + PAD at any level, base-template leaves over
# pinned base shape classes (review-D6 F1), arity 2/3/4/8 on real D0a chunks.
# Classes (pq-e2e-d7/work/classes.sh): A = {d1_00-h10006-s3, d1_00-h10013-s1},
# B = {d1_00-h10013-s2, -h10025-s0, -h10026-s0, -h10027-s0, -h10029-s0}; base proofs at the class
# shape for h10006-s3, h10013-s1 (A) and h10025-s0, h10027-s0 (B).
#  1. arity 2, depth 3 on h10006-s3 (class A; creates the setup) and h10027-s0 (class B, a member
#     that is not the class's defining dir; proved against the setup, must reproduce it byte for
#     byte); fresh-process negatives on both;
#  2. the template of h10013-s1 (class A's second member) against the step-1 setup (TEMPLATES_ONLY);
#  3. arity 3, 4. arity 4 (two SHA instances), 5. arity 8: depth 1 on h10006-s3, each with the P_*
#     shape probe over copies of its P_2 (P_* time estimated per committed cell); leaves reused from
#     the previous run where identical (NEARPROOF_TREE_REUSE_LEAVES; every reused leaf re-checked).
# Sequential, 8 threads, <= 40 GB.  usage: run_d7.sh [STEPS]
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d7}
export PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e} NEARPROOF_PQ_DEPS=$D
O=$D/bclass
CORP=/data/illia/nearproof-deps/corpora/d1run/d1
A1=$O/d1_00-h10006-s3; A2=$O/d1_00-h10013-s1; B1=$O/d1_00-h10025-s0; B2=$O/d1_00-h10027-s0
export CLASS_DIRS="$A1 $B1" NEARPROOF_TREE_CONFIRM="$A2 $B2"
claim() { echo "$CORP/${1#d1_}/claim.bin"; }
negs() { # TAG CHUNK OTHER_CHUNK
  python3 "$HERE/tree_negatives.py" "$D/$1/$(basename $2)" "$(claim $(basename $2))" "$(claim $(basename $3))" ${4:-} > "$D/$1/$(basename $2)/negatives.txt" 2>&1
  tail -1 "$D/$1/$(basename $2)/negatives.txt"
}
for s in ${1:-1 2 3 4 5}; do case $s in
1)
  "$HERE/run_tree.sh" tree-a2d3 2 3 "$A1" "$(claim d1_00-h10006-s3)" || exit 1
  "$HERE/run_tree.sh" tree-a2d3 2 3 "$B2" "$(claim d1_00-h10027-s0)" "$D/tree-a2d3/$(basename $A1)/SETUP.json" || exit 1
  negs tree-a2d3 $A1 $B2 "$D/tree-a2d3/$(basename $B2)"; negs tree-a2d3 $B2 $A1 "$D/tree-a2d3/$(basename $A1)"
  ;;
2)
  X=$D/tree-a2d3-A2-templates; rm -rf $X; mkdir -p $X
  NEARPROOF_TREE_SETUP=$D/tree-a2d3/$(basename $A1)/SETUP.json NEARPROOF_TREE_TEMPLATES_ONLY=1 NEARPROOF_ZK=1 NEARPROOF_TAPE_EVAL=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_ZK_FINAL=6 \
    RAYON_NUM_THREADS=8 taskset -c 8-15 "$PROVER" tree-prove "$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json" "$A2/public" $X "$A2" \
    "$ROOT/research/near-compression/final-soundness/calc/dkt_certs_o2.json" "$ROOT/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys" 2 3 $CLASS_DIRS > $X/prove.log 2>&1
  echo "A2_TEMPLATES rc=$? $(grep -h 'TREE_CHUNK_CLASS\|TREE_TEMPLATES_MATCH_FIXED_SETUP\|panicked' $X/prove.log | tr '\n' ' ')"
  ;;
3) NEARPROOF_TREE_STAR_PROBE=1 NEARPROOF_TREE_REUSE_LEAVES=$D/tree-a2d3/$(basename $A1) "$HERE/run_tree.sh" tree-a3d1 3 1 "$A1" "$(claim d1_00-h10006-s3)" && negs tree-a3d1 $A1 $B2 ;;
4) NEARPROOF_TREE_STAR_PROBE=1 NEARPROOF_TREE_REUSE_LEAVES=$D/tree-a3d1/$(basename $A1) "$HERE/run_tree.sh" tree-a4d1 4 1 "$A1" "$(claim d1_00-h10006-s3)" && negs tree-a4d1 $A1 $B2 ;;
5) NEARPROOF_TREE_STAR_PROBE=1 NEARPROOF_TREE_REUSE_LEAVES=$D/tree-a4d1/$(basename $A1) "$HERE/run_tree.sh" tree-a8d1 8 1 "$A1" "$(claim d1_00-h10006-s3)" && negs tree-a8d1 $A1 $B2 ;;
esac; done
echo D7_DONE
