#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-e2e}
"$HERE/../recursion/setup_cpu_fast_deps.sh"
python3 "$HERE/manifest.py" "$NEARPROOF_PQ_DEPS"
