#!/usr/bin/env bash
# E2E-D D-2 follow-ups on chunk 1 after run_zk4.sh zk5 (sequential, <= 10 threads):
#   zk5b  a second full-ZK FINAL proof of the same L4 (same witness, fresh randomness) -> zk-diff
#   zk5r274  full-ZK FINAL at a 274-bit per-round target (E2E-SOUNDNESS-BUDGET.md)
#   guess    witness-guessing distinguisher / two-witness test on the zk = 2 and zk = 5 packets
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
B=${PROVER:-$D/target/release/nearproof-chunk-e2e}
C=d1_00-h10006-s3
CHUNKS=$C "$HERE/run_zk4.sh" zk5b NEARPROOF_ZK_FINAL=5
"$B" zk-diff "$D/zk5/$C/FINAL.proof" "$D/zk5b/$C/FINAL.proof" > "$D/zk-diff-zk5.txt" 2>&1
CHUNKS=$C "$HERE/run_zk4.sh" zk5r274 NEARPROOF_ZK_FINAL=5 NEARPROOF_FINAL_RBR=274
"$HERE/run_zk_guess.sh" "$D/e2e/$C" "$D/zk5/$C" > "$D/zk-guess.txt" 2>&1
echo EXTRA_DONE
