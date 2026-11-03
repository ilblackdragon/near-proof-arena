#!/usr/bin/env bash
# Re-prove only the FINAL layer from an existing chain checkpoint (BASE.*, L<n>.*, hint, public)
# and verify the packet in a fresh process. Used to measure FINAL-only levers (e.g. NEARPROOF_ZK).
# usage: replay_final.sh OUT_WITH_CHECKPOINT N CLAIM_BIN
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
OUT=$(realpath "${1:?OUT}"); N=${2:?N}; CLAIM=$(realpath "${3:?claim.bin}")
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
K=$ROOT/research/near-compression/final-soundness
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
SP=$D/target-classical/release/examples/statepublic
export NEARPROOF_CHAIN_GEOM=${NEARPROOF_CHAIN_GEOM:-ns19lb6} NEARPROOF_TAPE_EVAL=${NEARPROOF_TAPE_EVAL:-1}
export HEAVY_MEM=${HEAVY_MEM:-32G} RAYON_NUM_THREADS=${RAYON_NUM_THREADS:-10}
CPUSET=${CPUSET:-8-15,24-25}
s=$(date +%s.%N)
taskset -c "$CPUSET" /data/illia/nearproof-deps/bin/heavy "$B" replay-final "$AIR" "$OUT/public" "$OUT" \
  "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" "$N" > "$OUT/final.log" 2>&1
echo "FINAL_REPLAY wall_s=$(echo "$(date +%s.%N) - $s" | bc)" | tee -a "$OUT/final.log"
RAYON_NUM_THREADS=1 taskset -c 8 "$B" verify "$AIR" "$CLAIM" "$SP" "$OUT/SETUP.json" "$(cat "$OUT/SETUP.sha256")" \
  "$OUT/FINAL.bundle" > "$OUT/verify.log" 2>&1
"$B" proof-sections "$OUT/FINAL.proof" | tee "$OUT/sections.txt"
grep -h "VERIFY_PROFILE_MS\|INDEPENDENT_VERIFY_OK" "$OUT/verify.log"
