#!/usr/bin/env bash
# Dependency tree for the e2e runs: the recursion patch stack up to the e2e layer
# (native/recursion/setup_e2e_verify_deps.sh: cpu-fast + e2e-verify.patch [+ zk-pcs.patch]),
# then the driver manifest. usage: setup_e2e.sh [DEPS_DIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
NATIVE=$HERE/../../native
export NEARPROOF_PQ_DEPS=${1:-${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}}
"$NATIVE/recursion/setup_e2e_verify_deps.sh"
python3 "$NATIVE/pq-chunk-e2e/manifest.py" "$NEARPROOF_PQ_DEPS"
echo "e2e deps OK: $NEARPROOF_PQ_DEPS"
