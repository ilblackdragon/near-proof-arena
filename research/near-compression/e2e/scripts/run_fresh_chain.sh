#!/usr/bin/env bash
# E2E-D milestone D-5, review-D4 F2: completeness under a fixed setup with a FRESH chain. Chunk 1's
# base is re-proved (base zk = 1: fresh randomness, so a fresh u and fresh L1..L4 transcripts),
# the chain is re-run, and FINAL is proved against the shape-pinned setup of run_zk6s.sh
# (NEARPROOF_FINAL_HEIGHTS). The new SETUP.json must be byte-identical, and the packet must verify
# in a fresh process. usage: run_fresh_chain.sh OUT FIXED_SETUP.json   (<= 10 threads)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
OUT=${1:?OUT}; FIXED=${2:?FIXED_SETUP.json}
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d5f}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
E=/data/illia/nearproof-deps/pq-e2e-d/e2e/d1_00-h10006-s3
C=/data/illia/nearproof-deps/corpora/d1run/d1/00-h10006-s3
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 NEARPROOF_ZK=1 NEARPROOF_ZK_FINAL=6
export RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10} HEAVY_MEM=${HEAVY_MEM:-40G}
rm -rf "$OUT"; mkdir -p "$OUT"; cp -r "$E/public" "$OUT/"
run() { taskset -c "${CPUSET:-8-15,24-25}" /data/illia/nearproof-deps/bin/heavy /usr/bin/time -v "$B" "$@"; }
run base "$AIR" "$E/dump" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/base.log" 2>&1
echo "BASE rc=$?"
NEARPROOF_FINAL_HEIGHTS=$FIXED run chain "$AIR" "$OUT/public" "$OUT" "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$OUT/chain.log" 2>&1
echo "CHAIN rc=$? $(grep -h 'L[0-9]_VERIFIED\|FINAL_PINNED' "$OUT/chain.log" | cut -c1-80 | tr '\n' ' ')"
cmp "$FIXED" "$OUT/SETUP.json" && echo "FRESH_CHAIN_SETUP_IDENTICAL"
RAYON_NUM_THREADS=1 taskset -c 8 "$B" verify "$AIR" "$C/claim.bin" unused "$FIXED" "$(sha256sum "$FIXED" | cut -d' ' -f1)" "$OUT/FINAL.bundle" 2>&1 \
  | grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_VERIFY_OK\|panicked"
cmp -s "$E/BASE.u.json" "$OUT/BASE.u.json" && echo "WARNING: same u as the original chain" || echo "FRESH_U (base point differs from the original chain)"
rm -f "$OUT"/L*.state.json "$OUT"/L*.vk.json
