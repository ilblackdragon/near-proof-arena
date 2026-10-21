#!/usr/bin/env bash
# R lane (in-circuit SWIRL verifier, SHA-384/Ext12): rebuild every dependency tree
# from pinned upstream sources plus the patches in ./patches.
#
#   NEARPROOF_PQ_DEPS   target root (default /data/illia/nearproof-deps/pq-recursion)
#
# Trees created under $NEARPROOF_PQ_DEPS:
#   stark-backend, plonky3-ext12   via ../setup_native_deps.sh (pinned, patched)
#   openvm-stock                   OpenVM v2.1.0-rc.1 + calibration test (milestone 1)
#   openvm-sha384                  OpenVM v2.1.0-rc.1 + SHA-384/Ext12 verifier port (milestone 2+),
#                                  workspace patched onto ../stark-backend and ../plonky3-ext12
#
# Idempotent: existing trees are verified against the pinned patch, never re-patched.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-recursion}
DEPS=$NEARPROOF_PQ_DEPS

"$HERE/../setup_native_deps.sh"

OPENVM_URL=https://github.com/openvm-org/openvm
OPENVM_REV=f08bf2836409f3c0a5f6b6cfe73eb177a8a3e8c8   # v2.1.0-rc.1

checkout_patched() {  # <dir> <patch>
  local dir=$1 patch=$2
  if [ ! -d "$dir/.git" ]; then
    local tmp
    tmp=$(mktemp -d "$DEPS/.openvm.XXXX")
    git -C "$tmp" init -q
    git -C "$tmp" fetch -q --depth 1 "$OPENVM_URL" "$OPENVM_REV"
    git -C "$tmp" checkout -q --detach FETCH_HEAD
    git -C "$tmp" apply "$patch"
    # Track new files so `git diff` reproduces the patch exactly.
    git -C "$tmp" add -N .
    mv "$tmp" "$dir"
  fi
  [ "$(git -C "$dir" rev-parse HEAD)" = "$OPENVM_REV" ] || { echo "$dir: wrong revision" >&2; exit 1; }
  # A pinned patch may contain successive edits to the same file. Compare the
  # resulting tree, not its textual diff layout. A separate index leaves the
  # user's checkout/index untouched and still rejects any content difference.
  local expected_index
  expected_index=$(mktemp "$DEPS/.expected-index.XXXX")
  rm "$expected_index"
  GIT_INDEX_FILE="$expected_index" git -C "$dir" read-tree HEAD
  if ! GIT_INDEX_FILE="$expected_index" git -C "$dir" apply --cached --whitespace=nowarn "$patch"; then
    rm -f "$expected_index"
    return 1
  fi
  if ! diff <(git -C "$dir" diff HEAD | grep -v '^index ') \
      <(GIT_INDEX_FILE="$expected_index" git -C "$dir" diff --cached HEAD | grep -v '^index ') >/dev/null; then
    rm -f "$expected_index"
    echo "$dir: working tree differs from $patch" >&2
    return 1
  fi
  rm -f "$expected_index"
}

checkout_patched "$DEPS/openvm-stock" "$HERE/patches/openvm-stock-calib.patch"
checkout_patched "$DEPS/openvm-sha384" "$HERE/patches/openvm-recursion-sha384.patch"

# The port carries a verbatim copy of the native config for differential tests.
cmp -s "$HERE/../../airbender/direct-wasm/native_sha384_config.rs" \
       "$DEPS/openvm-sha384/crates/recursion/src/sha384/native_ref.rs" \
  || { echo "native_ref.rs differs from airbender/direct-wasm/native_sha384_config.rs" >&2; exit 1; }

# openvm-sha384 builds against the unified research backend (levers + x15 + NV-lane additions).
NEARPROOF_PQ_DEPS="$DEPS" "$HERE/setup_unified_deps.sh"

echo "recursion deps OK: $DEPS"
