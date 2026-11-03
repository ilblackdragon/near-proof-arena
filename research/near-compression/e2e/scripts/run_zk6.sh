#!/usr/bin/env bash
# E2E-D milestone D-3 (2026-11-03): FINAL re-proved with zk = 6 (no stacked openings, WHIR batched
# with the stacking coefficients, extension-field stacking masks; ZK-ARGUMENT.md) from each D0a
# chunk's L4 checkpoint, then:
#   * fresh-process verify (5 x one core), soundness report, 21 negatives per chunk;
#   * chunk 1: a second proof of the same L4 (zk-diff), a 274-bit FINAL, and the
#     witness-guessing distinguisher / two-witness test.
# Sequential, <= 10 threads. The deps tree D must have e2e/<chunk> checkpoints (a symlink to the
# D-2 tree's e2e/ is enough: they are only copied) and target-classical/ (statepublic).
# usage: run_zk6.sh
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d3}
D=$NEARPROOF_PQ_DEPS
C=/data/illia/nearproof-deps/corpora
export PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
C1=d1_00-h10006-s3
"$HERE/run_zk4.sh" zk6 NEARPROOF_ZK_FINAL=6
cd "$D/zk6" || exit 1
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3" "$C/d1run/d1/00-h10007-s0" > neg1.log 2>&1; echo "NEG1 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10007-s0 "$C/d1run/d1/00-h10007-s0" "$C/d1run/d1/00-h10006-s3" > neg2.log 2>&1; echo "NEG2 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d2_05-h10042-s3 "$C/d2corpus.v2/d2/05-h10042-s3" "$C/d1run/d1/00-h10006-s3" > neg3.log 2>&1; echo "NEG3 rc=$?"
CHUNKS=$C1 "$HERE/run_zk4.sh" zk6b NEARPROOF_ZK_FINAL=6
"$PROVER" zk-diff "$D/zk6/$C1/FINAL.proof" "$D/zk6b/$C1/FINAL.proof" > "$D/zk-diff-zk6.txt" 2>&1
CHUNKS=$C1 "$HERE/run_zk4.sh" zk6r274 NEARPROOF_ZK_FINAL=6 NEARPROOF_FINAL_RBR=274
"$HERE/run_zk_guess.sh" "$D/zk6/$C1" > "$D/zk-guess-zk6.txt" 2>&1
echo ZK6_DONE
