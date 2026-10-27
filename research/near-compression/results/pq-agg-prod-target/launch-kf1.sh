#!/bin/bash
# DECISIVE TEST of the sole surviving depth-2 lever: k_first=1 for L2.
# Round 0 contributes 63% of L2's 9,764 merkle_nodes at 2^k_first=4 rows/query.
# k_first=1 halves rows/query -> if nodes scale, comps 10,021 -> ~6,700 -> fits 2^20.
# The delivered final layer already uses k_first=1 at 131 queries / 268.2 bits,
# so this should cost NO soundness. Everything else stays at production targets.
BIN=/data/illia/nearproof-deps/pq-agg/target-agg/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7
export CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
export EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
for P in PARENT PARENT2; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=18 ${P}_LOG_BLOWUP=7 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4 ${P}_X15=15
  export ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1 ${P}_GKR_DERIVE=1
  export ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_WIDE_POW=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1
  export ${P}_QUERY_POW=32 ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
done
# THE LEVER: k_first=1 on L2 only (L1 keeps the production k_first=2)
# PARENT_K1 deliberately UNSET: 0 means "fall back to k", matching production
export PARENT2_K1=1
export AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=20 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
