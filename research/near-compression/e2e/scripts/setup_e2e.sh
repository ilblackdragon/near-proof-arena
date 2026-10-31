#!/usr/bin/env bash
# Dependency tree for the e2e run: the pinned cpu-fast deps plus patches/e2e-verify.patch, then
# the driver manifest. usage: setup_e2e.sh [DEPS_DIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
NATIVE=$HERE/../../native
export NEARPROOF_PQ_DEPS=${1:-${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}}
D=$NEARPROOF_PQ_DEPS
if [ ! -f "$D/.e2e-overlay" ]; then
  "$NATIVE/recursion/setup_cpu_fast_deps.sh"
  (cd "$D" && patch -s -p1 < "$HERE/../patches/e2e-verify.patch")
  touch "$D/.e2e-overlay"
fi
python3 "$NATIVE/pq-chunk-e2e/manifest.py" "$D"
echo "e2e deps OK: $D"
