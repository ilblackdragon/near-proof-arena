#!/bin/bash
# Depth 3 at the geometry that MADE DEPTH 2 LEGAL (agg-d2-geom-ns19lb6.log, AGG_DEPTH2_OK).
#
# Depth 2 needed l_skip+n_stack+log_blowup = 2+19+6 = 27 with stacked height 2^21, because its
# SHA AIR reached log_height 21 (comps=8747).  Depth 3 aggregates two *NV* children exactly as
# depth 2 did (both L2 nodes verify 2 NV proofs of the same shape), so the depth law predicts a
# flat cost: the L3 SHA AIR should land at or near 2^21 and fit the same 2^21 stacked ceiling.
# If it does, depth d costs d levels and a 146-leaf (1 Pgas) tree needs log2(146)=8 levels.
#
# L1 proofs hit NEARPROOF_PROOF_CACHE, so this run proves only the L2/L3 nodes.
set -u
O=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/results/pq-agg-prod-target
CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
BIN=/var/tmp/pq-prod-target/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7

export NEARPROOF_DIGEST_BYTES=42
export NEARPROOF_COSET_LEAF=1
export NEARPROOF_TSTAR=1
export NEARPROOF_DIAG_GEOM=1
export NEARPROOF_PROOF_CACHE=$O/proof-cache

export AGG_DEPTH=3
# PARENT (level 1, App children): unchanged, so L1 proofs hit the cache.
export PARENT_L_SKIP=2 PARENT_N_STACK=18 PARENT_LOG_BLOWUP=7 PARENT_BITS=268 PARENT_LIST_M=64 PARENT_K=4
export PARENT_LOG_FINAL=7 PARENT_K1=1 PARENT_X15=15
export PARENT_MULTIPROOF=1 PARENT_KEEP_DOMAIN=1 PARENT_GRUEN_GKR=1 PARENT_GKR_DERIVE=1
export PARENT_NEXT_MASK=1 PARENT_GRUEN_ZC=1 PARENT_WIDE_POW=1 PARENT_TIGHT=1 PARENT_WHIR_Y=1
export PARENT_QUERY_POW=32 PARENT_COMMITS=1
export PARENT_DKT_CERTS=$CERT PARENT_DKT_EXCLUDE=$EXCL
# PARENT2/PARENT3 (Node children): the legal depth-2 geometry.
for P in PARENT2 PARENT3; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=19 ${P}_LOG_BLOWUP=6 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4
  export ${P}_LOG_FINAL=8 ${P}_K1=1 ${P}_X15=15
  export ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1 ${P}_GKR_DERIVE=1
  export ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_WIDE_POW=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1
  export ${P}_QUERY_POW=32 ${P}_COMMITS=1
  export ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
done
export AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=20 AGG_LOG_ROWS3=20 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
