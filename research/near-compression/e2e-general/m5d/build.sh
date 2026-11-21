#!/usr/bin/env bash
# Build the M5d Lean tool and the prover. Box rules: ≤ 8 threads, Lean ≤ 24 GB, prover builds ≤ 24 GB.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=/data/illia/nearproof-deps/e2e-m5d
TARGET_DIR=${TARGET_DIR:-$DEPS/target}
HEAVY="env HEAVY_MEM=${HEAVY_MEM:-24G} /data/illia/nearproof-deps/bin/heavy"
mkdir -p "$DEPS"
( cd "$HERE/lean" && $HEAVY lake build m5d-tool >/dev/null )
( cd "$HERE/prover" && CARGO_TARGET_DIR=$TARGET_DIR nice -n 10 $HEAVY cargo build --release --offline -j 8 )
