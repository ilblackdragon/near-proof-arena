#!/usr/bin/env bash
# [lane E, M11e] Regenerate the NvAir export (zk-formal/ZkFormal/PQ/NvAirExport.lean) from the
# current e2e-tree patch stack.
#
# Usage: setup.sh <repo root> [out file]
#   NEARPROOF_PQ_DEPS  private deps tree (default /data/illia/nearproof-deps/laneE-nv); built by
#                      setup_e2e_verify_deps.sh with E2E_ZK=1 E2E_TREE=1, i.e. openvm-sha384 @ f08bf28
#                      + openvm-recursion-sha384 + openvm-recursion-stream + openvm-recursion-cpu-fast
#                      + e2e-verify + zk-pcs + zk-piop + e2e-heights + e2e-tree (and the backend /
#                      plonky3 patches of those scripts).  Shared trees are refused by those scripts.
#   out file           default <repo>/zk-formal/ZkFormal/PQ/NvAirExport.lean
#
# nv_export.rs is installed as a #[cfg(test)] module `nv::nv_export` of the private tree (the only
# change outside the patch stack; setup_e2e_verify_deps.sh's reverse-apply check does not cover
# nv/mod.rs's appended line, nv/mod.rs is in e2e-tree.patch, so the module line is removed again
# after the run to keep the tree re-checkable).
set -euo pipefail
REPO=$(cd "${1:?repo root}" && pwd)
OUT=${2:-$REPO/zk-formal/ZkFormal/PQ/NvAirExport.lean}
R=$REPO/research/near-compression/native/recursion
P=$R/patches
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/laneE-nv}
D=$NEARPROOF_PQ_DEPS
if [ ! -f "$D/.e2e-tree-overlay" ]; then
  E2E_ZK=1 E2E_TREE=1 "$R/setup_e2e_verify_deps.sh"
else
  # setup_e2e_verify_deps.sh is not re-runnable on a finished tree (its cpu-fast step regenerates
  # stark-backend-cpu-fast.patch from the live backend, which the e2e patches have since changed),
  # so re-check only its last step: a copy of the touched files reverse-applies every e2e patch.
  CHK=$(mktemp -d /data/illia/nearproof-deps/tmp-laneE/.nvchk.XXXX); trap 'rm -rf "$CHK"' EXIT
  PS="e2e-verify zk-pcs zk-piop e2e-heights e2e-tree"
  for f in $(for p in $PS; do grep -h '^+++ b/' "$P/$p.patch"; done | sed 's|^+++ b/||' | sort -u); do
    [ -f "$D/$f" ] && { mkdir -p "$CHK/$(dirname "$f")"; cp "$D/$f" "$CHK/$f"; }
  done
  for p in $(echo $PS | tr ' ' '\n' | tac); do
    (cd "$CHK" && patch -s -p1 -R --no-backup-if-mismatch -E < "$P/$p.patch" >/dev/null) \
      || { echo "$D: tree does not contain $p.patch" >&2; exit 1; }
  done
  rm -rf "$CHK"; trap - EXIT
  echo "e2e-tree stack present: $D"
fi
cd "$D/openvm-sha384"
NV=crates/recursion/src/nv
cp "$R/nv-export/nv_export.rs" $NV/nv_export.rs
cleanup() { sed -i '/^\/\/ nv-export$/,+2d' $NV/mod.rs; rm -f $NV/nv_export.rs; }
trap cleanup EXIT
grep -q 'mod nv_export;' $NV/mod.rs || printf '// nv-export\n#[cfg(test)]\nmod nv_export;\n' >> $NV/mod.rs
h() { sha256sum "$1" | cut -c1-16; }
PH=""
for p in openvm-recursion-sha384 openvm-recursion-stream openvm-recursion-cpu-fast stark-backend-unified stark-backend-stream stark-backend-cpu-fast e2e-verify zk-pcs zk-piop e2e-heights e2e-tree; do
  PH="$PH $p.patch $(h "$P/$p.patch")…,"
done
SH=""
for f in uair.rs isa.rs glue.rs transcript2.rs hash.rs circuit.rs builder.rs tree.rs agg.rs; do
  SH="$SH nv/$f $(h $NV/$f)…,"
done
HDR="Source: openvm-sha384 @ f08bf28 + the e2e-tree stack (setup_e2e_verify_deps.sh, E2E_ZK=1 E2E_TREE=1); patch sha256:$PH sources sha256:$SH sha384/compress4_air.rs $(h crates/recursion/src/sha384/compress4_air.rs)…; exporter nv_export.rs $(h $NV/nv_export.rs)….
Circuit: NvCircuit::new(3, 17, 1) (one compression instance), keygen with parent_params_debug and max_constraint_degree = max(layout degree, 6).
Regenerate: \`research/near-compression/native/recursion/nv-export/setup.sh <repo>\` (cargo test --release -p openvm-recursion-circuit --lib nv::nv_export)."
export NV_EXPORT_HEADER="$HDR"
export NV_EXPORT_OUT=$OUT
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$D/target}
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-8}
nice cargo test --release -p openvm-recursion-circuit --lib nv::nv_export -- --nocapture
