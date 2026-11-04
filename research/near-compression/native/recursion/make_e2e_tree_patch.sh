#!/usr/bin/env bash
# Regenerate patches/e2e-tree.patch (lane E2E-D milestone D-5, 2026-11-03):
#   = BASE (an E2E_ZK=1 tree with e2e-heights.patch: cpu-fast + e2e-verify + zk-pcs + zk-piop +
#     e2e-heights, e.g. pq-e2e-d5f) -> DEPS (the live D-5 tree pq-e2e-d5)   over TREE_FILES
# Contents: the aggregation overlay (nv/agg.rs, ChainStart, restart_transcript, RangeStmt / tag 9;
# formerly openvm-recursion-agg.patch on f08bf28) rebased onto the e2e/zk stack, with the program
# binding of NV children restored (the pinned agg overlay had emptied that branch) and made
# multi-child (BIND for child 0, root_i = root_0 for the others, anchor sets, forced anchors);
# nv/tree.rs (normaliser, PAD, node, wrap; vd::verify_wrap); HeightProfile over several chains;
# test fixes (WhirLevers zk). The aggregation overlay changes NvAir (the ChainStart bus) and the NV
# program (a ChainStart row), so chains proved without it (D0a L1..L4) cannot be BIND-extended
# with it: D0a FINAL replays use the e2e-heights tree (pq-e2e-d5f).
# D-6 (2026-11-04, DEPS = pq-e2e-d6): + build_base_leaf / Builder::capture_statement (the base-template
# leaf, lane A/B leaf prototype), review-D5 D5-2 (program part index after a preprocessed commit),
# D5-5 (fixed-height tables pinned at their height), D5-1 constraint-level tree negatives.
# Applied by setup_e2e_verify_deps.sh after e2e-heights.patch when E2E_TREE=1.
# usage: make_e2e_tree_patch.sh [BASE] [DEPS] [OUTDIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
BASE=${1:-/data/illia/nearproof-deps/pq-e2e-d5f}
DEPS=${2:-/data/illia/nearproof-deps/pq-e2e-d6}
OUTDIR=${3:-$HERE/patches}
SB=stark-backend-unified/crates
R=openvm-sha384/crates/recursion/src
TREE_FILES="$SB/stark-backend/src/prover/stacked_pcs.rs
$R/nv/agg.rs
$R/nv/agg_tests.rs
$R/nv/tree.rs
$R/nv/tree_tests.rs
$R/nv/builder.rs
$R/nv/circuit.rs
$R/nv/glue.rs
$R/nv/isa.rs
$R/nv/mod.rs
$R/nv/transcript2.rs
$R/nv/uair.rs
$R/nv/verifier.rs
$R/nv/vd.rs
$R/nv/tests.rs
$R/nv/stream_tests.rs
$R/sha384/config.rs"
: > "$OUTDIR/e2e-tree.patch"
for f in $TREE_FILES; do
  src="$BASE/$f"; [ -f "$src" ] || src=/dev/null
  (cd / && diff -uN --label "a/$f" --label "b/$f" "$src" "$DEPS/$f") >> "$OUTDIR/e2e-tree.patch" || true
done
sha256sum "$OUTDIR/e2e-tree.patch"
