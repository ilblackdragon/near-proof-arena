#!/usr/bin/env bash
# [lane E, M11e] Regenerate zk-formal/ZkFormal/PQ/NvAirExport.lean from the pinned NV crate.
#
# Usage: setup.sh <repo root> [work dir]
#   SRC   pq-agg tree to copy (default /data/illia/nearproof-deps/pq-agg); never modified.
#   work  private copy + target dir (default /data/illia/nearproof-deps/tmp-laneE/nvx).
#
# The source tree is openvm-sha384 @ f08bf28 + patches/openvm-recursion-sha384.patch +
# patches/openvm-recursion-agg.patch (patches/README-agg-patch.md: byte-identical on the agg files
# to pq-agg/openvm-sha384).  We copy pq-agg (without .git/target), check that the agg patch
# reverse-applies cleanly, install nv_export.rs as a test module and run it.
set -euo pipefail
REPO=$(cd "${1:?repo root}" && pwd)
W=${2:-/data/illia/nearproof-deps/tmp-laneE/nvx}
SRC=${SRC:-/data/illia/nearproof-deps/pq-agg}
P=$REPO/research/near-compression/native/recursion/patches
mkdir -p "$W"
rsync -a --delete --exclude .git --exclude target "$SRC/openvm-sha384/" "$W/openvm-sha384/"
ln -sfn "$SRC/stark-backend-unified" "$W/stark-backend-unified"
ln -sfn "$SRC/plonky3-ext12" "$W/plonky3-ext12"
cd "$W/openvm-sha384"
patch -p1 -R --dry-run -s < "$P/openvm-recursion-agg.patch" >/dev/null
NV=crates/recursion/src/nv
cp "$REPO/research/near-compression/native/recursion/nv-export/nv_export.rs" $NV/nv_export.rs
grep -q 'mod nv_export;' $NV/mod.rs || printf '#[cfg(test)]\nmod nv_export;\n' >> $NV/mod.rs
h() { sha256sum "$1" | cut -c1-16; }
HDR="Source: openvm-sha384 @ f08bf28 + openvm-recursion-sha384.patch (sha256 $(h "$P/openvm-recursion-sha384.patch")…) + openvm-recursion-agg.patch (sha256 $(h "$P/openvm-recursion-agg.patch")…); nv/uair.rs sha256 $(h $NV/uair.rs)…, nv/isa.rs $(h $NV/isa.rs)…, nv/glue.rs $(h $NV/glue.rs)…, nv/transcript2.rs $(h $NV/transcript2.rs)…, nv/hash.rs $(h $NV/hash.rs)…, nv/circuit.rs $(h $NV/circuit.rs)…; exporter nv_export.rs $(h $NV/nv_export.rs)….
Regenerate: \`research/near-compression/native/recursion/nv-export/setup.sh <repo>\` (cargo test --release -p openvm-recursion-circuit nv_export)."
export NV_EXPORT_HEADER="$HDR"
export NV_EXPORT_OUT=$REPO/zk-formal/ZkFormal/PQ/NvAirExport.lean
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$W/target}
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-8}
cargo test --release -p openvm-recursion-circuit --lib nv::nv_export -- --nocapture
