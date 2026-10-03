#!/usr/bin/env bash
# Build recipe: run by the judge as `bash build-recipe/build.sh` from the
# package root, inside a sandbox with NO network, a fresh $HOME and
# SOURCE_DATE_EPOCH=0. It runs twice on independent copies; every output listed
# in candidate.toml [build].outputs must be bit-identical (BUILD_REPRODUCIBLE).
set -euo pipefail

ROOT="$(pwd)"
export CARGO_HOME="${HOME}/cargo-home"     # fresh; nothing from the host
export CARGO_TARGET_DIR="${ROOT}/source/target"
export CARGO_NET_OFFLINE=true
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
# Strip build-path dependence from the binaries.
export RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo -C strip=symbols"

# The lock copy in dependency-locks/ must match what we build with.
cmp -s source/Cargo.lock dependency-locks/Cargo.lock || {
  echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2
  exit 1
}

( cd source && cargo build --release --locked --offline --bins )

mkdir -p out
for bin in prepare prove verify; do
  install -m 0755 "source/target/release/${bin}" "out/${bin}"
done
