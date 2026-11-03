#!/usr/bin/env bash
# E2E verifier layer (lane E2E-D, 2026-11-03): the cpu-fast deps (setup_cpu_fast_deps.sh) plus
#   patches/e2e-verify.patch  TAPE bound by evaluation at the base stacking point (L1 statement
#                             digest covers (u, TAPE*(u)); lever NEARPROOF_TAPE_EVAL=1), and the
#                             final program check reusing the batch point of the verification
#                             just performed. Soundness: research/near-compression/e2e/VERIFIER-PATCH.md.
#   patches/zk-pcs.patch      (only with E2E_ZK=1) PCS-level hiding for a layer whose WHIR lever
#                             `zk` is set: random reserved rows in every stacked column and random
#                             mask columns in the common-main commitment. Off (zk = 0) it is inert.
#   patches/zk-piop.patch     (only with E2E_ZK=1) PIOP masking (`zk >= 4`): masked GKR, masked
#                             batch sumcheck with column masks, masked stacking reduction
#                             (research/near-compression/e2e/ZK-ARGUMENT.md). Inert for zk < 4.
#                             zk = 6 (D-3): WHIR batched with the stacking coefficients (no
#                             stacked openings), extension-field stacking masks; plus the review
#                             fixes (layout termination, proof-shape errors, verify_with_point).
#                             Regenerate with make_zk_piop_patch.sh.
#   patches/e2e-heights.patch (only with E2E_ZK=1; D-5, review-D4) FINAL heights pinned from the
#                             shape (HeightProfile, shape_pinned_heights), the FS job counter, a
#                             loud per-proof tight floor. Regenerate with make_e2e_heights_patch.sh.
#   patches/e2e-tree.patch    (only with E2E_ZK=1 E2E_TREE=1; D-5) the aggregation overlay rebased
#                             onto this stack with program binding restored and multi-child, the
#                             chunk-independent tree + wrap (nv/tree.rs), shape-pinned heights,
#                             the FS job counter. Regenerate with make_e2e_tree_patch.sh.
# Applied with `patch -p1` from the deps root. Idempotent: an overlaid tree is checked by
# reverse-applying each patch in a dry run (the tree must contain exactly the patch's hunks).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
D=$NEARPROOF_PQ_DEPS
case "$D" in */pq-recursion|*/pq-native|*/pq-stream|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
PATCHES="e2e-verify"
[ "${E2E_ZK:-1}" = 1 ] && PATCHES="$PATCHES zk-pcs zk-piop e2e-heights"
[ "${E2E_ZK:-1}" = 1 ] && [ "${E2E_TREE:-0}" = 1 ] && PATCHES="$PATCHES e2e-tree"
"$HERE/setup_cpu_fast_deps.sh"
for p in $PATCHES; do
  f="$HERE/patches/$p.patch"
  if [ ! -f "$D/.$p-overlay" ]; then
    (cd "$D" && patch -s -p1 --no-backup-if-mismatch < "$f")
    touch "$D/.$p-overlay"
  fi
done
# check: a copy of the touched files must reverse-apply every patch, last first
CHK=$(mktemp -d /data/illia/nearproof-deps/.e2echk.XXXX); trap 'rm -rf "$CHK"' EXIT
for f in $(for p in $PATCHES; do grep -h '^+++ b/' "$HERE/patches/$p.patch"; done | sed 's|^+++ b/||' | sort -u); do
  [ -f "$D/$f" ] && { mkdir -p "$CHK/$(dirname "$f")"; cp "$D/$f" "$CHK/$f"; }
done
for p in $(echo $PATCHES | tr ' ' '\n' | tac); do
  (cd "$CHK" && patch -s -p1 -R --no-backup-if-mismatch -E < "$HERE/patches/$p.patch" >/dev/null) \
    || { echo "$D: tree does not contain $p.patch" >&2; exit 1; }
done
echo "e2e verify deps OK ($PATCHES): $D"
