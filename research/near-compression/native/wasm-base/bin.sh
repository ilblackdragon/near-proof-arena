#!/usr/bin/env bash
# Resolve the `nearproof-wasm-base` binary for the harness scripts, and refuse a stale one.
#
# Why this file exists: the harness used to default to a binary under
# $NEARPROOF_PQ_DEPS, but the crate builds into its own `target/release/`, so the
# default path usually did not exist. When a binary *was* found it could be older
# than the sources, and a stale binary has produced false KAT failures three times
# (e.g. `sharegkat` panicking at tracegen.rs out-of-bounds because it predated the
# REG chip). Prefer the in-repo build, then the deps build, and always compare
# against the newest source file.
#
# Usage:  source bin.sh; BIN=$(resolve_bin) || exit 1
# Override: WASMBASE_BIN=/path/to/binary

resolve_bin() {
  local here src newest=0 newest_name="" candidate
  here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)

  # Newest source file / manifest: the binary must be at least this new.
  for src in "$here"/src/*.rs "$here"/Cargo.toml; do
    [ -f "$src" ] || continue
    if [ "$src" -nt "$newest_name" ] || [ -z "$newest_name" ]; then
      newest_name=$src
    fi
  done

  if [ -n "${WASMBASE_BIN:-}" ]; then
    candidates=("$WASMBASE_BIN")
  else
    candidates=(
      "$here/target/release/nearproof-wasm-base"
      "${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-wasm-base}/target/release/nearproof-wasm-base"
    )
  fi

  for candidate in "${candidates[@]}"; do
    [ -x "$candidate" ] || continue
    if [ -n "$newest_name" ] && [ "$newest_name" -nt "$candidate" ]; then
      echo "stale binary: $candidate" >&2
      echo "  $(basename "$newest_name") is newer; rebuild with:" >&2
      echo "    (cd $here && cargo build --release)" >&2
      return 1
    fi
    printf '%s\n' "$candidate"
    return 0
  done

  echo "nearproof-wasm-base not found; looked in:" >&2
  printf '  %s\n' "${candidates[@]}" >&2
  echo "build it with: (cd $here && cargo build --release)" >&2
  return 1
}
