#!/usr/bin/env bash
# E2E-D milestone D-5 (2026-11-03), review-D4 F1/F2: FINAL re-proved with zk = 6 and the FINAL
# heights pinned from the SHAPE (circuit::shape_pinned_heights: used rows minus the rows the L4
# transcript's rejection sampling added, plus the slack for J_max rejections at 2^-192), from the
# chunks' L4 checkpoints; then a second run with the SHA AIR's log height pinned one above
# (NEARPROOF_FINAL_LOG_BUMP=1: the log-height padding path). Fresh-process verify, soundness,
# the height negatives. Sequential, <= 8 threads. usage: run_zk6s.sh
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d5f}
D=$NEARPROOF_PQ_DEPS
C=/data/illia/nearproof-deps/corpora
export PROVER=${PROVER:-$D/target/release/nearproof-chunk-e2e}
[ -e "$D/e2e" ] || ln -s /data/illia/nearproof-deps/pq-e2e-d/e2e "$D/e2e"
"$HERE/run_zk4.sh" zk6s NEARPROOF_ZK_FINAL=6
CHUNKS=d1_00-h10006-s3 "$HERE/run_zk4.sh" zk6sb NEARPROOF_ZK_FINAL=6 NEARPROOF_FINAL_LOG_BUMP=1
cd "$D/zk6sb" || exit 1
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3" "$C/d1run/d1/00-h10007-s0" > neg1.log 2>&1; echo "NEG1 rc=$?"
for r in zk6s/d1_00-h10006-s3 zk6s/d1_00-h10007-s0 zk6s/d2_05-h10042-s3 zk6sb/d1_00-h10006-s3; do
  echo "## $r $(grep -h FINAL_SHAPE_PIN "$D/$r/final.log" | cut -c1-300)"
  "${FS_PROVER:-/data/illia/nearproof-deps/pq-e2e-d5/target/release/nearproof-chunk-e2e}" fs-count "$D/$r/SETUP.json" "$D/$r/FINAL.bundle" 1 2>&1 | grep FS_COUNT
done
echo ZK6S_DONE
