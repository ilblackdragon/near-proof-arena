#!/bin/bash
# Depth 2 at PRODUCTION HASH LEVERS + production WHIR params, with pre-prove geometry.
# The only change vs launch-d2-hashprod.sh: NEARPROOF_DIAG_GEOM=1 so the compression split
# is printed BEFORE prove_mats (the LayoutHeightExceeded panic currently destroys it),
# plus NEARPROOF_PROOF_CACHE so L1 child proofs are reused on later iterations.
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
for P in PARENT PARENT2; do
  export ${P}_L_SKIP=2 ${P}_N_STACK=18 ${P}_LOG_BLOWUP=7 ${P}_BITS=268 ${P}_LIST_M=64 ${P}_K=4
  export ${P}_LOG_FINAL=7 ${P}_K1=1 ${P}_X15=15
  export ${P}_MULTIPROOF=1 ${P}_KEEP_DOMAIN=1 ${P}_GRUEN_GKR=1 ${P}_GKR_DERIVE=1
  export ${P}_NEXT_MASK=1 ${P}_GRUEN_ZC=1 ${P}_WIDE_POW=1 ${P}_TIGHT=1 ${P}_WHIR_Y=1
  export ${P}_QUERY_POW=32 ${P}_COMMITS=1
  export ${P}_DKT_CERTS=$CERT ${P}_DKT_EXCLUDE=$EXCL
done
export AGG_LOG_ROWS1=18 AGG_LOG_ROWS2=20 NV_PROG_LOG=19 NEARPROOF_STREAM_COMMIT=1
exec "$BIN" agg_chain_depth_n --ignored --nocapture
