#!/usr/bin/env bash
# lane/pq-cpu-prover: the NV deps with the streamed-commit overlay (setup_stream_deps.sh), plus the
# fast CPU prover overlay:
#   patches/stark-backend-cpu-fast.patch  (cpu-backend/src/fast/*: SoA Ext12, MLE rounds, GKR, ...)
#   patches/plonky3-ext12-simd.patch      (Ext12 under AVX2/AVX-512 builds: p3 had no SIMD path for
#                                          degree 12 and panicked; one-dot-product Ext12 mul)
#   patches/openvm-recursion-cpu-fast.patch (8-lane AVX-512 SHA-384: grinding, Merkle leaves/nodes)
#
# P4 (cached commitments - TAPE, CODE - entering the statement digest V_d checks) is part of
# patches/openvm-recursion-sha384.patch since 11bfed3d4, so the former
# `patches/p4-tape-statement.patch` step is gone; only its test is appended below.
# Every fast path is byte-identical to the original code; NEARPROOF_CPU_FAST=0 selects the original
# code at run time. Build with RUSTFLAGS="-C target-cpu=native" for the AVX-512 packing.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-cpu2}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-native|*/pq-stream|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
if [ ! -f "$DEPS/.cpu-fast-overlay" ]; then
  "$HERE/setup_stream_deps.sh"
  git -C "$DEPS/stark-backend-unified" apply "$HERE/patches/stark-backend-cpu-fast.patch"
  git -C "$DEPS/stark-backend-unified" add -N .
  (cd "$DEPS/plonky3-ext12" && patch -s -p1 < "$HERE/patches/plonky3-ext12-simd.patch")
  git -C "$DEPS/openvm-sha384" apply "$HERE/patches/openvm-recursion-cpu-fast.patch"
  # the P4 test (`nv_stmt_covers_cached_root`): append to the NV test module
  # (the P4 *code* patch is folded into openvm-recursion-sha384.patch since 11bfed3d4)
  T="$DEPS/openvm-sha384/crates/recursion/src/nv/tests.rs"
  grep -q nv_stmt_covers_cached_root "$T" || { printf '\n' >> "$T"; cat "$HERE/patches/p4-statement-test.rs" >> "$T"; }
  git -C "$DEPS/openvm-sha384" add -N .
  touch "$DEPS/.cpu-fast-overlay"
fi
# verify: the overlay regenerated from the live trees equals the pinned patches
CHK=$(mktemp -d); trap 'rm -rf "$CHK"' EXIT
CPU_FAST_PATCH_OUT=$CHK "$HERE/make_cpu_fast_patches.sh" >/dev/null
for p in stark-backend-cpu-fast plonky3-ext12-simd openvm-recursion-cpu-fast; do
  cmp -s "$CHK/$p.patch" "$HERE/patches/$p.patch" || { echo "$p: live tree differs from patch" >&2; exit 1; }
done
echo "cpu-fast deps OK: $DEPS"
