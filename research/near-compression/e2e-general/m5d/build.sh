#!/usr/bin/env bash
# Build the M5d Lean tool and the prover. Box rules: ≤ 8 threads, Lean ≤ 24 GB, prover builds ≤ 24 GB.
# LEAN=0 skips the lake build (use the m5d-tool already built, e.g. while lean/ is being edited).
# The prover (G-2) builds against lane B's frozen copy of the verifier's backend
# (/data/illia/nearproof-deps/laneB-t1/deps: lane D's pq-e2e-d9 stark-backend-unified + plonky3-ext12).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=/data/illia/nearproof-deps/e2e-m5d
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-24G} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$DEPS"
[ "${LEAN:-1}" = 0 ] || ( cd "$HERE/lean" && $HEAVY lake build m5d-tool >/dev/null )
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 )
