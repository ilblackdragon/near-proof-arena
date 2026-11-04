#!/usr/bin/env bash
# Regenerate patches/e2e-heights.patch (lane E2E-D milestone D-5, 2026-11-03):
#   = BASE (an E2E_ZK=1 D-4 tree: cpu-fast + e2e-verify + zk-pcs + zk-piop, e.g. pq-e2e-d4h)
#     -> DEPS (pq-e2e-d5f)                                                  over HEIGHT_FILES
# Contents (review of D-4, "review-D4"):
#   F1  circuit::HeightProfile + shape_pinned_heights: FINAL heights pinned from the shape alone
#       (used rows minus the rows the child transcript's rejection sampling added, plus the slack
#       for J_max rejections at 2^-eps); Builder::height_profile;
#   F5  sha384::config::FS_JOBS: a counter of the transcript's SHA-384 evaluations (R);
#   the tight floor is consumed per proof and a mismatch / unused floor is a prover panic.
# Applied by setup_e2e_verify_deps.sh after zk-piop.patch (E2E_ZK=1). The driver's FINAL path
# (pq-chunk-e2e chain) needs it.
# usage: make_e2e_heights_patch.sh [BASE] [DEPS] [OUTDIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
BASE=${1:-/data/illia/nearproof-deps/pq-e2e-d4h}
DEPS=${2:-/data/illia/nearproof-deps/pq-e2e-d5f}
OUTDIR=${3:-$HERE/patches}
SB=stark-backend-unified/crates
R=openvm-sha384/crates/recursion/src
HEIGHT_FILES="$SB/stark-backend/src/prover/stacked_pcs.rs
$R/nv/builder.rs
$R/nv/circuit.rs
$R/sha384/config.rs"
: > "$OUTDIR/e2e-heights.patch"
for f in $HEIGHT_FILES; do
  src="$BASE/$f"; [ -f "$src" ] || src=/dev/null
  (cd / && diff -uN --label "a/$f" --label "b/$f" "$src" "$DEPS/$f") >> "$OUTDIR/e2e-heights.patch" || true
done
sha256sum "$OUTDIR/e2e-heights.patch"
