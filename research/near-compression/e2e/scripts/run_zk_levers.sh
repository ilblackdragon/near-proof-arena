#!/usr/bin/env bash
# E2E-D 2026-11-03 lever measurements after the 3-chunk run (sequential, <= 10 threads):
#   rz3   FINAL replay with zk = 3 (slice-splitting packing)
#   r274  FINAL replay with zk = 2 at a 274-bit per-round target (E2E-SOUNDNESS-BUDGET.md)
#   ubase a second zk = 1 base proof of chunk 1 (same witness): its u must differ
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=/data/illia/nearproof-deps/pq-e2e-d
C=/data/illia/nearproof-deps/corpora
S=$D/e2e/d1_00-h10006-s3
B=$D/target-zk3/release/nearproof-chunk-e2e
K=$ROOT/research/near-compression/final-soundness
AIR=$ROOT/examples/np-udr-stark-v2/source/near-air-v3.json
export NEARPROOF_PQ_DEPS=$D
prep() { rm -rf "$1"; mkdir -p "$1"; cp -r "$S/public" "$S/BASE.proof" "$S/BASE.vk.json" "$S/L4.proof" "$S/L4.vk.json" "$S/L4.state.json" "$S/hint.bin" "$1/"; }
run_replay() {  # dir env...
  local r=$1; shift
  prep "$r"
  env "$@" PROVER="$B" "$HERE/replay_final.sh" "$r" 4 "$C/d1run/d1/00-h10006-s3/claim.bin" > "$r.out" 2>&1
  echo "REPLAY $r rc=$?"
}
run_replay "$D/rz3" NEARPROOF_ZK_FINAL=3
run_replay "$D/r274" NEARPROOF_FINAL_RBR=274
"$B" soundness "$D/r274/SETUP.json" > "$D/r274/soundness.txt" 2>&1
mkdir -p "$D/ubase"
NEARPROOF_ZK=1 NEARPROOF_CHAIN_GEOM=ns19lb6 NEARPROOF_TAPE_EVAL=1 RAYON_NUM_THREADS=10 HEAVY_MEM=32G \
  taskset -c 8-15,24-25 /data/illia/nearproof-deps/bin/heavy "$B" base "$AIR" "$S/dump" "$D/ubase" \
  "$K/calc/dkt_certs_o2.json" "$K/lean/DKTCertsO2_big.keys" > "$D/ubase/base.log" 2>&1
echo "UBASE rc=$?"
"$B" zk-diff "$S/BASE.proof" "$D/ubase/BASE.proof" > "$D/zk-diff-base.txt" 2>&1
echo LEVERS_DONE
