#!/bin/bash
# Depth 2 geometry escape: PARENT2 n_stack 18->19, log_blowup 7->6.
# l_skip + n_stack + log_blowup stays 2+19+6 = 27 = the field's two-adic bound, so the
# WHIR evaluation domain n = 15*2^27 is UNCHANGED while the stacked ceiling rises 2^20 -> 2^21.
# L2's SHA AIR is at log_height 21 (comps=8747, rows=1119616), so this is the only change needed.
# PARENT (level 1) is untouched, so L1_0/L1_1 hit the proof cache and only L2 is re-proved.
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

export AGG_DEPTH=2
# PARENT = level 1, unchanged from agg-d2-geom.log so the L1 proof cache hits.
export PARENT_L_SKIP=2 PARENT_N_STACK=18 PARENT_LOG_BLOWUP=7 PARENT_BITS=268 PARENT_LIST_M=64 PARENT_K=4
export PARENT_LOG_FINAL=7 PARENT_K1=1 PARENT_X15=15
export PARENT_MULTIPROOF=1 PARENT_KEEP_DOMAIN=1 PARENT_GRUEN_GKR=1 PARENT_GKR_DERIVE=1
export PARENT_NEXT_MASK=1 PARENT_GRUEN_ZC=1 PARENT_WIDE_POW=1 PARENT_TIGHT=1 PARENT_WHIR_Y=1
export PARENT_QUERY_POW=32 PARENT_COMMITS=1
export PARENT_DKT_CERTS=$CERT PARENT_DKT_EXCLUDE=$EXCL
# PARENT2 = level 2, the geometry escape: 2+19+6 = 27, ceiling 2^21.
export PARENT2_L_SKIP=2 PARENT2_N_STACK=19 PARENT2_LOG_BLOWUP=6 PARENT2_BITS=268 PARENT2_LIST_M=64 PARENT2_K=4
# h=21, k_first=1: num_rounds = 1 + ceil((h-lf-1)/4); lf=8 keeps 4 rounds (lf=7 would add a 5th).
export PARENT2_LOG_FINAL=8 PARENT2_K1=1 PARENT2_X15=15
export PARENT2_MULTIPROOF=1 PARENT2_KEEP_DOMAIN=1 PARENT2_GRUEN_GKR=1 PARENT2_GKR_DERIVE=1
export PARENT2_NEXT_MASK=1 PARENT2_GRUEN_ZC=1 PARENT2_WIDE_POW=1 PARENT2_TIGHT=1 PARENT2_WHIR_Y=1
export PARENT2_QUERY_POW=32 PARENT2_COMMITS=1
export PARENT2_DKT_CERTS=$CERT PARENT2_DKT_EXCLUDE=$EXCL
export AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=20 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
