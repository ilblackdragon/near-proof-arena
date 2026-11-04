#!/usr/bin/env bash
# Rebuild only the chunk driver against the e2e deps tree (CPUSET, JOBS jobs; default CPUs 8-15, 8 jobs).
set -euo pipefail
D=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d8}
export PATH="$HOME/.cargo/bin:$PATH"
CARGO_TARGET_DIR="$D/target" CARGO_ENCODED_RUSTFLAGS='-Ctarget-cpu=native' taskset -c "${CPUSET:-8-15}" \
  cargo build --release --locked -j "${JOBS:-8}" --manifest-path "$D/chunk-driver/Cargo.toml" > "$D/build-driver.log" 2>&1 || { grep -E "^error|error\[" -A5 "$D/build-driver.log" | head -40; exit 1; }
