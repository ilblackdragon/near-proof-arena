#!/usr/bin/env bash
# Build the static (musl) arena binaries that go into images:
#   arena-init    -> guest rootfs (/sbin/arena-init)
#   arena-fc-shim -> delivery container entrypoint
# Paths are remapped and symbols stripped so the output does not depend on
# the checkout location. Prints the output directory.
set -euo pipefail
repo=$(cd "$(dirname "$0")/../.." && pwd)
target=x86_64-unknown-linux-musl
export RUSTFLAGS="-C strip=symbols -C target-feature=+crt-static --remap-path-prefix=$repo=/src --remap-path-prefix=$HOME/.cargo=/cargo --remap-path-prefix=$HOME/.rustup=/rustup"
export CARGO_TARGET_DIR=${ARENA_STATIC_TARGET_DIR:-$repo/target/static}
cd "$repo"
cargo build -q -j "${CARGO_JOBS:-8}" --release --target "$target" -p arena-init -p arena-fc-shim >&2
echo "$CARGO_TARGET_DIR/$target/release"
