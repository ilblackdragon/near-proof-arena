#!/bin/bash
# The full lever set cut L2's SHA AIR from 2^22 to 2^21 (measured panic log_height:21 vs 20).
# So log_blowup=6 with n_stack=19 gives stacked height 2+19 = 21 -- exactly what L2 needs,
# and cheaper in queries than lb=5 (which gives 22 but needs 260 queries at X15=1).
# Legal check: l_skip + n_stack + log_blowup = 2 + 19 + 6 = 27 <= 27. OK.
set -u
O=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/results/pq-agg-prod-target
CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
BIN=/data/illia/nearproof-deps/pq-agg/target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7

export AGG_DEPTH=2
for P in PARENT PARENT2; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=19 ${P}_LOG_BLOWUP=6 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4 ${P}_X15=15
  export ${P}_QUERY_POW=32 ${P}_WIDE_POW=1 ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1
  export ${P}_GKR_DERIVE=1 ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1 ${P}_COMMITS=1
  export ${P}_LOG_FINAL=6 ${P}_K1=2
  export ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
done
export AGG_LOG_ROWS1=19 AGG_LOG_ROWS2=21 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
