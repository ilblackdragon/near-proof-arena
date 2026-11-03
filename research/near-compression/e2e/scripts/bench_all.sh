#!/usr/bin/env bash
# Verifier timing for the three e2e runs plus the delivered v1 packet (old protocol, for comparison).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
E=/data/illia/nearproof-deps/pq-e2e-zk/e2e
C=/data/illia/nearproof-deps/corpora
for r in d1_00-h10006-s3:d1run/d1/00-h10006-s3 d1_00-h10007-s0:d1run/d1/00-h10007-s0 d2_05-h10042-s3:d2corpus.v2/d2/05-h10042-s3; do
  echo "== ${r%%:*}"
  bash "$HERE/bench_verify.sh" "$E/${r%%:*}" "$C/${r#*:}" "${REPS:-7}" 2>&1 | sed 's/INDEPENDENT_VERIFY_OK[^t]*threads/threads/; s/VERIFY_PROFILE_MS //'
done
echo "== delivered opt-baseline-8 (v1 packet: TAPE commitment recomputed), new binary"
bash "$HERE/bench_verify.sh" /data/illia/nearproof-deps/pq-chunk-e2e/runs/opt-baseline-8 "$ROOT/oracle/fixtures/v3/public-d0a/d0/00-h10004-s3" 3 2>&1 | sed 's/INDEPENDENT_VERIFY_OK[^t]*threads/threads/; s/VERIFY_PROFILE_MS //'
