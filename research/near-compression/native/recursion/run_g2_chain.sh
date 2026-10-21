#!/usr/bin/env bash
# lane/pq-stream-commit: the sound G2 chain (lane/pq-recursion-sha384 9159123be: cached program
# commitment, anchors (M, C_M) + tight-height floor, BIND, FINAL single-commitment pinned by V_d)
# with the streamed commitments and the fast CPU prover (lane/pq-cpu-prover 6134476fc), real settings
# (268 bits = 236 + z 32 wide PoW, 42-B digests, coset leaves, x15, every lever, m = 64 + O-2 with the
# kernel-only DKT certificates). nv_chain: no phase A (natural heights), L1.. until a level binds its
# child by BIND, then FINAL (own WHIR shape, FINAL_*) + V_d + (NV_VD_FORGE=1) the forged final.
#   run_g2_chain.sh <tag>
# env: penultimate PB PNS PK PK1 PLF (7 18 4 2 6), final FB FNS FK FK1 FLF (7 18 4 1 7), NV_LEVELS (2),
#      NV_LOG_ROWS (18), NV_PROG_LOG (17), THREADS (16), CPUSET (8-15,24-31), HEAVY_MEM (60G), BIN, CERTS, EXCL, OUT,
#      INTERACTION_LOG (28: this gate's recorded budget; the production default is 2^30)
set -uo pipefail
TAG=$1
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-stream-g2}
BIN=${BIN:-$DEPS/bin/nv-g2s}
K=/data/illia/nearproof-wt/pq-dkt-verify/research/near-compression/final-soundness
CERTS=${CERTS:-$K/calc/dkt_certs_o2.json}
EXCL=${EXCL:-$K/lean/DKTCertsO2_big.keys}
OUT=${OUT:-$DEPS/ckpt/$TAG}
T=${THREADS:-16}
CPUSET=${CPUSET:-8-15,24-31}
mkdir -p "$OUT"
LEV="X15=15 KEEP_DOMAIN=1 MULTIPROOF=1 GRUEN_GKR=1 GKR_DERIVE=1 GRUEN_ZC=1 NEXT_MASK=1 WHIR_Y=1 TIGHT=1 WIDE_POW=1 QUERY_POW=32 BITS=268 LIST_M=64 L_SKIP=2"
P=""; F=""
for x in $LEV; do P="$P PARENT_$x"; F="$F FINAL_$x"; done
cd "$DEPS/openvm-sha384/crates/recursion"
{ date -u; free -g | head -2; sha256sum "$CERTS" "$EXCL" "$BIN"; } > "$OUT/run.log"
env HEAVY_MEM=${HEAVY_MEM:-60G} taskset -c "$CPUSET" /data/illia/nearproof-deps/bin/heavy \
  env RAYON_NUM_THREADS=$T NEARPROOF_CPU_FAST=1 NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1 NEARPROOF_MEMPROF=1 \
  NEARPROOF_STREAM_COMMIT=1 NEARPROOF_STREAM_DROP=${NEARPROOF_STREAM_DROP:-4} NEARPROOF_DKT_CERTS="$CERTS" NEARPROOF_DKT_EXCLUDE="$EXCL" \
  NV_PHASE_A=0 NV_LEVELS=${NV_LEVELS:-2} NV_VD_FORGE=${NV_VD_FORGE:-1} NV_LOG_ROWS=${NV_LOG_ROWS:-18} NV_PROG_LOG=${NV_PROG_LOG:-17} NV_SAVE_DIR="$OUT" \
  PARENT_INTERACTION_LOG=${INTERACTION_LOG:-28} FINAL_INTERACTION_LOG=${INTERACTION_LOG:-28} \
  $P PARENT_LOG_BLOWUP=${PB:-7} PARENT_N_STACK=${PNS:-18} PARENT_K=${PK:-4} PARENT_K1=${PK1:-2} PARENT_LOG_FINAL=${PLF:-6} \
  $F FINAL_LOG_BLOWUP=${FB:-7} FINAL_N_STACK=${FNS:-18} FINAL_K=${FK:-4} FINAL_K1=${FK1:-1} FINAL_LOG_FINAL=${FLF:-7} \
  /usr/bin/time -v "$BIN" nv::tests::nv_chain --ignored --exact --nocapture --test-threads 1 >> "$OUT/run.log" 2>&1
result=$?
echo "EXIT $result" >> "$OUT/run.log"
exit "$result"
