#!/usr/bin/env bash
# E2E-D milestone D-5 (2026-11-03; D-6: CLASS_ROOT, TAG, OUT_ROOT): chunk-independent aggregation tree + ZK wrap on D0a chunks.
# Leaves: the chunk's D0a template leaf (normaliser of its converged chain proof L4) + PAD leaves
# up to ARITY^DEPTH; DEPTH levels of ARITY-ary nodes; the wrap (final domain, zk = 6, heights
# pinned from the shape). The template set holds all three D0a shape classes + PAD, so the wrap
# setup is the same for every chunk: chunk 1 creates it, chunk 2 is proved against it
# (NEARPROOF_TREE_SETUP) and must reproduce it byte for byte. Then fresh-process verification.
# usage: run_tree.sh [ARITY] [DEPTH]   (sequential, <= 8 threads)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d5}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
# the template class dirs (each: L4.proof + L4.vk.json + chain.log, BASE.*, public, hint.bin). D-6:
# CLASS_ROOT=pq-e2e-d6/classes (chains with shape floors); default: the D-4 chains of D-5
E=${CLASS_ROOT:-/data/illia/nearproof-deps/pq-e2e-d/e2e}
C=/data/illia/nearproof-deps/corpora
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
A=${1:-2}; DEP=${2:-1}
TAG=${TAG:-tree-a${A}d${DEP}}
declare -A CLAIM=(
  [d1_00-h10006-s3]=$C/d1run/d1/00-h10006-s3/claim.bin
  [d1_00-h10007-s0]=$C/d1run/d1/00-h10007-s0/claim.bin
  [d2_05-h10042-s3]=$C/d2corpus.v2/d2/05-h10042-s3/claim.bin
)
CLASSES="$E/d1_00-h10006-s3 $E/d1_00-h10007-s0 $E/d2_05-h10042-s3"
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-8} HEAVY_MEM=${HEAVY_MEM:-56G}
# the D0a chain geometry (the L4 template proofs), tape-eval, wrap zk = 6; tree layer ns20lb5
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export NEARPROOF_TREE_GEOM=${NEARPROOF_TREE_GEOM:-ns20lb5}
SETUP_ENV=()
for c in ${CHUNKS:-d1_00-h10006-s3 d2_05-h10042-s3}; do
  R=${OUT_ROOT:-$D}/$TAG/$c
  rm -rf "$R"; mkdir -p "$R"
  echo "LOAD_BEFORE $c $(cut -d' ' -f1-3 /proc/loadavg)"
  # shellcheck disable=SC2086
  env "${SETUP_ENV[@]}" taskset -c "${CPUSET:-8-15}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
    "$B" tree-prove "$AIR" "$E/$c/public" "$R" "$E/$c" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$A" "$DEP" $CLASSES \
    > "$R/prove.log" 2>&1
  echo "TREE $c rc=$? $(grep -h 'TREE_FIXED_SETUP_IDENTICAL\|Maximum resident' "$R/prove.log" | tr '\n' ' ')"
  grep -h "TREE_WRAP_VERIFIED" "$R/prove.log" | cut -c1-400
  for i in 1 2 3; do
    RAYON_NUM_THREADS=1 taskset -c 8 "$B" tree-verify "$AIR" "${CLAIM[$c]}" "$R/SETUP.json" "$(cat "$R/SETUP.sha256")" "$R/WRAP.bundle" 2>&1 \
      | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_TREE_VERIFY_OK\|panicked"
  done
  "$B" soundness "$R/SETUP.json" > "$R/soundness.txt" 2>&1
  [ ${#SETUP_ENV[@]} -eq 0 ] && SETUP_ENV=(NEARPROOF_TREE_SETUP="$R/SETUP.json")
  echo "LOAD_AFTER $c $(cut -d' ' -f1-3 /proc/loadavg)"
done
echo TREE_DONE
