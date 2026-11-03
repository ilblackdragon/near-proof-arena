#!/usr/bin/env bash
# Rebuild only the chunk driver against the e2e deps tree (CPUs 8-15,24-31, 8 jobs).
set -euo pipefail
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-zk}
export PATH="$HOME/.cargo/bin:$PATH"
CARGO_TARGET_DIR="$D/target" CARGO_ENCODED_RUSTFLAGS='-Ctarget-cpu=native' taskset -c 8-15,24-31 \
  cargo build --release --locked -j ${JOBS:-8} --manifest-path "$D/chunk-driver/Cargo.toml" 2>&1 | grep -E "^(error|warning: unused)|Finished|error\[" | head -40
