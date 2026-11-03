#!/usr/bin/env bash
# E2E verifier layer (lane E2E-D, 2026-11-03): the cpu-fast deps (setup_cpu_fast_deps.sh) plus
#   patches/e2e-verify.patch  TAPE bound by evaluation at the base stacking point (L1 statement
#                             digest covers (u, TAPE*(u)); lever NEARPROOF_TAPE_EVAL=1), and the
#                             final program check reusing the batch point of the verification
#                             just performed. Soundness: research/near-compression/e2e/VERIFIER-PATCH.md.
#   patches/zk-pcs.patch      (only with E2E_ZK=1) PCS-level hiding for a layer whose WHIR lever
#                             `zk` is set: random reserved rows in every stacked column and random
#                             mask columns in the common-main commitment. Off (zk = 0) it is inert.
# Applied with `patch -p1` from the deps root. Idempotent: an overlaid tree is checked by
# reverse-applying each patch in a dry run (the tree must contain exactly the patch's hunks).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-e2e-d}
D=$NEARPROOF_PQ_DEPS
case "$D" in */pq-recursion|*/pq-native|*/pq-stream|*/openvm) echo "refusing shared tree" >&2; exit 1;; esac
PATCHES="e2e-verify"
[ "${E2E_ZK:-1}" = 1 ] && PATCHES="$PATCHES zk-pcs"
"$HERE/setup_cpu_fast_deps.sh"
for p in $PATCHES; do
  f="$HERE/patches/$p.patch"
  if [ ! -f "$D/.$p-overlay" ]; then
    (cd "$D" && patch -s -p1 --no-backup-if-mismatch < "$f")
    touch "$D/.$p-overlay"
  fi
  (cd "$D" && patch -s -p1 -R --dry-run < "$f" >/dev/null) || { echo "$D: tree does not contain $p.patch" >&2; exit 1; }
done
echo "e2e verify deps OK ($PATCHES): $D"
