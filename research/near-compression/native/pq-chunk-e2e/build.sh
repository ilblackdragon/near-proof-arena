#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../../.." && pwd)
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-e2e}
export PATH="$HOME/.cargo/bin:$PATH"
python3 "$HERE/manifest.py" "$D"
export HEAVY_MEM=${HEAVY_MEM:-16G}
HEAVY=/data/illia/nearproof-deps/bin/heavy
CPUSET=${CPUSET:-8-15,24-31}
JOBS=${BUILD_JOBS:-8}
CARGO_TARGET_DIR="$D/target" CARGO_ENCODED_RUSTFLAGS='-Ctarget-cpu=native' taskset -c "$CPUSET" "$HEAVY" \
  cargo build --release --locked -j "$JOBS" --manifest-path "$D/chunk-driver/Cargo.toml"
CARGO_TARGET_DIR="$D/target-classical" taskset -c "$CPUSET" "$HEAVY" \
  cargo build --release --locked -j "$JOBS" --manifest-path "$ROOT/examples/np-udr-stark-v2/source/Cargo.toml" \
  --example statedump --example statepublic
