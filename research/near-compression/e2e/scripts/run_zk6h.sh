#!/usr/bin/env bash
# E2E-D milestone D-4 (2026-11-03): obligation H. FINAL re-proved with zk = 6 and the FINAL trace
# heights pinned in the setup (`Setup::final_heights`, V_d equality check before any other work,
# the prover pads to them) from each D0a chunk's L4 checkpoint, then:
#   * fresh-process verify (5 x one core), soundness report, negatives per chunk (the 21 of D-3
#     plus the height negatives of negatives.py);
#   * chunk 1: a second proof against the FIRST run's setup (`NEARPROOF_FINAL_HEIGHTS`: the
#     fixed-setup prover; its SETUP.json must be byte-identical), zk-diff of the two proofs, and
#     the witness-guessing distinguisher / two-witness test.
# Sequential, <= 10 threads. usage: run_zk6h.sh
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d4h}
D=$NEARPROOF_PQ_DEPS
C=/data/illia/nearproof-deps/corpora
export PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
C1=d1_00-h10006-s3
"$HERE/run_zk4.sh" zk6h NEARPROOF_ZK_FINAL=6
cd "$D/zk6h" || exit 1
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3" "$C/d1run/d1/00-h10007-s0" > neg1.log 2>&1; echo "NEG1 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10007-s0 "$C/d1run/d1/00-h10007-s0" "$C/d1run/d1/00-h10006-s3" > neg2.log 2>&1; echo "NEG2 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d2_05-h10042-s3 "$C/d2corpus.v2/d2/05-h10042-s3" "$C/d1run/d1/00-h10006-s3" > neg3.log 2>&1; echo "NEG3 rc=$?"
cp "$D/zk6h/$C1/SETUP.json" "$D/zk6h-setup-$C1.json"
CHUNKS=$C1 "$HERE/run_zk4.sh" zk6hb NEARPROOF_ZK_FINAL=6 NEARPROOF_FINAL_HEIGHTS="$D/zk6h-setup-$C1.json"
cmp "$D/zk6h/$C1/SETUP.json" "$D/zk6hb/$C1/SETUP.json" && echo "FIXED_SETUP_IDENTICAL $C1"
"$PROVER" zk-diff "$D/zk6h/$C1/FINAL.proof" "$D/zk6hb/$C1/FINAL.proof" > "$D/zk-diff-zk6h.txt" 2>&1
"$HERE/run_zk_guess.sh" "$D/zk6h/$C1" > "$D/zk-guess-zk6h.txt" 2>&1
echo ZK6H_DONE
