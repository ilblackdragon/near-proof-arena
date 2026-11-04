#!/usr/bin/env bash
# E2E-D milestone D-5, review-D4 F2 with shape floors: chunk 1's chain re-run twice with every
# level's tight floor and the FINAL heights pinned from the shape (NEARPROOF_CHAIN_SHAPE_FLOORS=1,
# the default): (A) from the original base proof, creating the setup; (B) from a fresh base proof
# (base zk = 1: another u, other transcripts), proving FINAL against A's setup. B's SETUP.json must
# be byte-identical to A's and B's packet must verify against A's pinned setup in a fresh process.
# usage: run_shape_chain.sh OUT_A OUT_B FRESH_BASE_DIR   (<= 10 threads)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
A=${1:?OUT_A}; BB=${2:?OUT_B}; FRESH=${3:?FRESH_BASE_DIR}
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d5f}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
E=/data/illia/nearproof-deps/pq-e2e-d/e2e/d1_00-h10006-s3
C=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10} HEAVY_MEM=${HEAVY_MEM:-40G}
run() { taskset -c "${CPUSET:-8-15,24-25}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v "$B" "$@"; }
for X in "$A" "$BB"; do rm -rf "$X"; mkdir -p "$X"; done
cp -r "$E/public" "$E/BASE.proof" "$E/BASE.vk.json" "$E/hint.bin" "$A/"
cp -r "$FRESH/public" "$FRESH/BASE.proof" "$FRESH/BASE.vk.json" "$FRESH/hint.bin" "$BB/"
run chain "$AIR" "$A/public" "$A" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$A/chain.log" 2>&1
echo "CHAIN_A rc=$? $(grep -h 'L1_SHAPE_FLOOR\|_ANCHOR\|FINAL_SHAPE_PIN' "$A/chain.log" | cut -c1-110 | tr '\n' ' ')"
NEARPROOF_FINAL_HEIGHTS=$A/SETUP.json run chain "$AIR" "$BB/public" "$BB" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$BB/chain.log" 2>&1
echo "CHAIN_B rc=$? $(grep -h 'L1_SHAPE_FLOOR\|_ANCHOR\|FINAL_PINNED' "$BB/chain.log" | cut -c1-110 | tr '\n' ' ')"
cmp "$A/SETUP.json" "$BB/SETUP.json" && echo "FRESH_CHAIN_SETUP_IDENTICAL"
for X in "$A" "$BB"; do
  RAYON_NUM_THREADS=1 taskset -c 8 "$B" verify "$AIR" "$C/claim.bin" unused "$A/SETUP.json" "$(cat "$A/SETUP.sha256")" "$X/FINAL.bundle" 2>&1 \
    | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_VERIFY_OK\|panicked"
done
cmp -s "$A/BASE.u.json" "$BB/BASE.u.json" && echo "WARNING: same u" || echo "FRESH_U (B's base point differs from A's)"
rm -f "$A"/L*.state.json "$BB"/L*.state.json "$A"/L*.vk.json "$BB"/L*.vk.json
