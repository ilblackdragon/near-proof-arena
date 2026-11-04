#!/usr/bin/env bash
# E2E-D milestone D-6: re-prove the D0a shape classes' chains with shape floors
# (NEARPROOF_CHAIN_SHAPE_FLOORS=1, the default since D-5) from their D-4 base proofs, so that every
# template L4 (and its program root C_L4, the tree's template anchor) is a function of the class's
# shape only. Keeps L4.proof + L4.vk.json (the tree's template input), the FINAL packet, SETUP.
# usage: run_shape_classes.sh OUT_ROOT CHUNK...   (sequential, <= 10 threads)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
O=${1:?OUT_ROOT}; shift
B=${PROVER:-/data/illia/nearproof-deps/pq-e2e-d5f/target/release/nearproof-chunk-e2e}
E=/data/illia/nearproof-deps/pq-e2e-d/e2e
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
declare -A CLAIM=(
  [d1_00-h10006-s3]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3/claim.bin
  [d1_00-h10007-s0]=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10007-s0/claim.bin
  [d2_05-h10042-s3]=/data/illia/nearproof-deps/corpora/d2corpus.v2/d2/05-h10042-s3/claim.bin
)
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10} HEAVY_MEM=${HEAVY_MEM:-40G}
for c in "$@"; do
  X=$O/$c
  rm -rf "$X"; mkdir -p "$X"
  cp -r "$E/$c/public" "$E/$c/BASE.proof" "$E/$c/BASE.vk.json" "$E/$c/hint.bin" "$X/"
  echo "LOAD_BEFORE $c $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "${CPUSET:-8-15,24-25}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v \
    "$B" chain "$AIR" "$X/public" "$X" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$X/chain.log" 2>&1
  echo "CHAIN $c rc=$? $(grep -h 'L1_SHAPE_FLOOR\|FINAL_SHAPE_PIN\|Maximum resident' "$X/chain.log" | cut -c1-120 | tr '\n' ' ')"
  for i in 1 2 3; do
    RAYON_NUM_THREADS=1 taskset -c 8 "$B" verify "$AIR" "${CLAIM[$c]}" unused "$X/SETUP.json" "$(cat "$X/SETUP.sha256")" "$X/FINAL.bundle" 2>&1 \
      | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_VERIFY_OK\|panicked"
  done
  rm -f "$X"/L*.state.json "$X"/L[123].vk.json
done
echo CLASSES_DONE
