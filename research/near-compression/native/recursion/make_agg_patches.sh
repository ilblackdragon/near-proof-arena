#!/usr/bin/env bash
# lane/pq-agg-rebase: regenerate the aggregation overlay from a working deps tree set up by
# setup_agg_deps.sh:
#   patches/openvm-recursion-agg.patch   on top of the full base chain
#                                        (sha384 + stream + cpu-fast, i.e. setup_cpu_fast_deps.sh)
# The overlay adds nv/agg.rs (the n-to-1 node), its tests, the ChainStart op / bus, and the
# build_agg hook in build_verifier (`bind_child`).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-agg}
OUT=${AGG_PATCH_OUT:-$HERE/patches}
T=$(mktemp -d "$DEPS/.mkagg.XXXX")
trap 'rm -rf "$T"' EXIT
gitq() { git -C "$1" -c user.name=nearproof -c user.email=nearproof@localhost "${@:2}"; }

mkdir "$T/ov"; cp -a "$DEPS/openvm-sha384/." "$T/ov/"; rm -rf "$T/ov/target"
gitq "$T/ov" reset -q; gitq "$T/ov" checkout -q -- .; gitq "$T/ov" clean -qfdx
# the overlay sits on the whole base chain, in the order the setup scripts apply it
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-sha384.patch" 2>/dev/null
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-stream.patch"
gitq "$T/ov" apply "$HERE/patches/openvm-recursion-cpu-fast.patch"
gitq "$T/ov" add -A; gitq "$T/ov" commit -q -m base
rsync -a --delete --exclude target --exclude .git --exclude .agg-overlay --exclude .cpu-fast-overlay \
  --exclude .stream-overlay --exclude .verify.\* --exclude .mkagg.\* --exclude .aggverify.\* \
  --exclude crates/recursion/examples "$DEPS/openvm-sha384/" "$T/ov/"
gitq "$T/ov" add -A
gitq "$T/ov" diff --cached HEAD | grep -v '^index ' > "$OUT/openvm-recursion-agg.patch"
wc -l "$OUT/openvm-recursion-agg.patch"
