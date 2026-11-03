#!/usr/bin/env bash
# The driver needs the e2e verifier layer (tape-eval statement, take_last_*_point hooks), so it
# builds on setup_e2e_verify_deps.sh, not on the bare cpu-fast tree.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-e2e}
"$HERE/../recursion/setup_e2e_verify_deps.sh"
python3 "$HERE/manifest.py" "$NEARPROOF_PQ_DEPS"
