#!/bin/bash
# Depth-2 at log_blowup=5 with the FULL production lever set (X15=15, all levers on).
# This is the uncontaminated test of the "lower blowup to <=5" escape. The earlier lb=5 run
# used X15=1 (domain 2^27), which conflated the blowup change with the X15 bug.
set -u
O=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/results/pq-agg-prod-target
CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
BIN=/data/illia/nearproof-deps/pq-agg/target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7

export AGG_DEPTH=2
for P in PARENT PARENT2; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=20 ${P}_LOG_BLOWUP=5 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4 ${P}_X15=15
  export ${P}_QUERY_POW=32 ${P}_WIDE_POW=1 ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1
  export ${P}_GKR_DERIVE=1 ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1 ${P}_COMMITS=1
  export ${P}_LOG_FINAL=6 ${P}_K1=2
  export ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
done
export AGG_LOG_ROWS1=20 AGG_LOG_ROWS2=22 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
