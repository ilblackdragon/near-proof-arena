#!/usr/bin/env bash
# A-T1: build the segment prover against the STACK's backend (lane D's `pq-chunk-e2e` deps,
# $NEARPROOF_PQ_DEPS default /data/illia/nearproof-deps/pq-chunk-e2e) instead of this crate's own
# pinned copy (`pq-wasm-base`), so template leaves are proved and their vks hashed by the verifier's
# backend.  The sources are this crate's; only the dependency paths differ.  The source builds
# unchanged against both backends.
#   build_stack.sh [crate_dir] [target_dir]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-e2e}
C=${1:-/data/illia/nearproof-deps/e2e-laneA/at1/wb-stack}
TGT=${2:-/data/illia/nearproof-deps/e2e-laneA/at1/target-stack}
mkdir -p "$C"
sed -e "s#/data/illia/nearproof-deps/pq-wasm-base/#$DEPS/#g" "$HERE/Cargo.toml" > "$C/Cargo.toml"
printf '\n[[bin]]\nname = "nearproof-wasm-base"\npath = "%s/src/main.rs"\n' "$HERE" >> "$C/Cargo.toml"
cp "$HERE/Cargo.lock" "$C/"
cd "$C" && CARGO_TARGET_DIR=$TGT cargo build --release --offline -j "${JOBS:-4}"
echo "$TGT/release/nearproof-wasm-base"
