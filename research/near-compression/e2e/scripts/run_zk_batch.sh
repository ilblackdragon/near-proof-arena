#!/usr/bin/env bash
# E2E-D 2026-11-03: (1) a second FINAL replay from the same L4 checkpoint as rf0-nosplit (same
# witness, fresh randomness) for the zk-diff hiding check; (2) the three chunks end to end with
# NEARPROOF_ZK=1; (3) negatives per chunk. Sequential, <= 10 threads.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=/data/illia/nearproof-deps/pq-e2e-d
C=/data/illia/nearproof-deps/corpora
S=/data/illia/nearproof-deps/pq-e2e-zk/e2e/d1_00-h10006-s3
if [ "${SKIP_REPLAY:-0}" != 1 ]; then
rm -rf "$D/rf2"; mkdir -p "$D/rf2"
cp -r "$S/public" "$S/BASE.proof" "$S/BASE.vk.json" "$S/L4.proof" "$S/L4.vk.json" "$S/L4.state.json" "$S/hint.bin" "$D/rf2/"
"$HERE/replay_final.sh" "$D/rf2" 4 "$C/d1run/d1/00-h10006-s3/claim.bin" > "$D/rf2.out" 2>&1
echo "REPLAY rf2 rc=$?"
"$D/target/release/nearproof-chunk-e2e" zk-diff "$D/rf0-nosplit/FINAL.proof" "$D/rf2/FINAL.proof" > "$D/zk-diff-replay.txt" 2>&1
echo "ZKDIFF rc=$?"
fi
"$HERE/batch3.sh" "$D/e2e"
cd "$D/e2e" || exit 1
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10006-s3 "$C/d1run/d1/00-h10006-s3" "$C/d1run/d1/00-h10007-s0" --wrong-witness > neg1.log 2>&1; echo "NEG1 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d1_00-h10007-s0 "$C/d1run/d1/00-h10007-s0" "$C/d1run/d1/00-h10006-s3" --wrong-witness > neg2.log 2>&1; echo "NEG2 rc=$?"
RAYON_NUM_THREADS=8 python3 "$HERE/negatives.py" d2_05-h10042-s3 "$C/d2corpus.v2/d2/05-h10042-s3" "$C/d1run/d1/00-h10006-s3" --wrong-witness > neg3.log 2>&1; echo "NEG3 rc=$?"
echo ALL_DONE
