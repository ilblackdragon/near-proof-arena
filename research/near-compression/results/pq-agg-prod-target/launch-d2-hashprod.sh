#!/bin/bash
# Depth 2 at PRODUCTION HASH LEVERS + production WHIR params.
#
# Why this is a new configuration: every earlier depth-2 run omitted
# NEARPROOF_DIGEST_BYTES / NEARPROOF_COSET_LEAF, so it silently used the defaults
# (d=48, coset_leaf=0).  The delivered production chain (run_cpu_chain.sh and the
# stream/g2 launch scripts) sets NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1.
# The measured node counts prove the difference independently of the scripts:
#   delivered chain: 27 merkle nodes/query at nbits=23  -> 23+4      -> coset_leaf=1
#   every d2 log   : 42 merkle nodes/query at nbits=23  -> 15+23+4   -> coset_leaf=0
#
# Expected from the compression model (docs/logs/pq-agg-sha-compression-accounting-2026-10-24.md):
#   coset_leaf=0: 9764 merkle + 3048 leaf = 12813 comps -> 2^21   (measured, panics)
#   coset_leaf=1: 6968 merkle + 3048 leaf = 10017 comps -> 2^21   (predicted)
# so this run is expected to STILL panic at log_height 21.  It is run anyway because
# (a) it is the first depth-2 attempt on production levers, and (b) the panic's
# log_height and the measured merkle_nodes settle the model one way or the other.
#
# Purpose: confirm/refute the 10,017 prediction, and produce the first
# production-hash-lever depth-2 node proof if the prediction is wrong.
set -u
O=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/results/pq-agg-prod-target
CERT=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/calc/dkt_certs_o2.json
EXCL=/data/illia/nearproof-wt/pq-chunk-e2e/research/near-compression/final-soundness/lean/DKTCertsO2_big.keys
BIN=/var/tmp/pq-prod-target/release/deps/openvm_recursion_circuit-e8a84b4284f8a0d7

# --- the hash levers production actually uses (this is the new part) ---
export NEARPROOF_DIGEST_BYTES=42
export NEARPROOF_COSET_LEAF=1
export NEARPROOF_TSTAR=1

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
