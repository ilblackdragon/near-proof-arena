#!/usr/bin/env bash
# lane/pq-agg-rebase: the aggregation / n-to-1 node overlay.
#
#   setup_cpu_fast_deps.sh        the full base chain (native, unified, recursion, stream, cpu-fast)
#   patches/openvm-recursion-agg.patch
#                                 the nv/agg.rs node, its tests, the ChainStart op + bus, and the
#                                 `bind_child` hook in build_verifier (program binding for NV
#                                 children of an aggregation node)
#
# The overlay used to sit on openvm-recursion-sha384.patch alone, i.e. before G2, so it stopped
# applying when G2 landed.  It is now generated against the full chain by make_agg_patches.sh.
#
#   NEARPROOF_PQ_DEPS   target root (default /data/illia/nearproof-deps/pq-agg; never a shared tree)
# Idempotent: an existing overlaid tree is verified against base + overlay, never re-patched.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-agg}
DEPS=$NEARPROOF_PQ_DEPS
case "$DEPS" in */pq-recursion|*/pq-native|*/pq-stream|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
AGG=$HERE/patches/openvm-recursion-agg.patch
T=$DEPS/openvm-sha384
if [ ! -f "$T/.agg-overlay" ]; then
  "$HERE/setup_cpu_fast_deps.sh"
  git -C "$T" apply "$AGG"
  git -C "$T" add -N .
  touch "$T/.agg-overlay"
fi
# verify: the overlay regenerated from the live tree equals the pinned patch
CHK=$(mktemp -d "$DEPS/.aggverify.XXXX")
trap 'rm -rf "$CHK"' EXIT
AGG_PATCH_OUT=$CHK NEARPROOF_PQ_DEPS="$DEPS" "$HERE/make_agg_patches.sh" >/dev/null
cmp -s "$CHK/openvm-recursion-agg.patch" "$AGG" \
  || { echo "$T differs from base + agg overlay (regenerate with make_agg_patches.sh)" >&2; exit 1; }
echo "agg deps OK: $DEPS"
