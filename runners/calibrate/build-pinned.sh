#!/usr/bin/env bash
# Reproducible build of the pinned calibration binary (BENCHMARK_SPEC §6.1):
# static musl, path prefixes remapped, no rustc wrapper. The digest it prints
# is what a challenge pins in measurement.calibration.binary_digest; the
# expected checksum is the line the binary prints.
set -euo pipefail
cd "$(dirname "$0")/../.."
out=${CARGO_TARGET_DIR:-$PWD/target}
RUSTFLAGS="--remap-path-prefix=$PWD=/src --remap-path-prefix=$HOME/.cargo=/cargo" RUSTC_WRAPPER= \
  cargo build -q --release --locked --target x86_64-unknown-linux-musl -p arena-calibrate
b="$out/x86_64-unknown-linux-musl/release/arena-calibrate"
echo "rustc: $(rustc --version)"
echo "binary_digest: sha256:$(sha256sum "$b" | cut -d' ' -f1)"
echo "expected_checksum: $("$b" | cut -d' ' -f2)"
