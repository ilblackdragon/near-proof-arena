#!/bin/bash
# Depth 2 at the EXACT production WHIR schedule of the delivered final layer.
# The 276,269 B depth-1 measurement (agg-prod-qpow32.log) used queries [41,38,29,23],
# which requires BOTH LOG_FINAL=7 and K1=1. Earlier d2 scripts omitted LOG_FINAL, so
# they ran 5 rounds [44,31,25,21,18] -- NOT production. This script fixes that.
# Purpose: with diagnostics on, report which AIR overflows and by how much.
BIN=/data/illia/nearproof-deps/pq-agg/target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7
export CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
export EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
for P in PARENT PARENT2; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=18 ${P}_LOG_BLOWUP=7 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4
  export ${P}_LOG_FINAL=7 ${P}_K1=1 ${P}_X15=15
  export ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1 ${P}_GKR_DERIVE=1
  export ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_WIDE_POW=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1
  export ${P}_QUERY_POW=32 ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
  # COMMITS=1 is the production final-layer value (program_part=false). The default for the
  # PARENT prefix is 2, which raises the agreement error and pushes round 0 to 44 queries
  # with first_order=false -- NOT production's [41,38,29,23].
  export ${P}_COMMITS=1
done
export AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=20 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
