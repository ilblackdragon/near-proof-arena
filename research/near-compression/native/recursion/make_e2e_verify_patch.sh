#!/usr/bin/env bash
# Regenerate the e2e layer patches of this directory from a live tree:
#   patches/e2e-verify.patch = PRISTINE -> PRISTINE+e2e  over E2E_FILES
#   patches/zk-pcs.patch     = PRISTINE+e2e-verify.patch -> DEPS over ZK_FILES
# PRISTINE = a fresh setup_cpu_fast_deps.sh tree, DEPS = the live e2e tree.
# Applied by setup_e2e_verify_deps.sh with `patch -p1` from the deps root.
# usage: make_e2e_verify_patch.sh [PRISTINE] [DEPS] [OUTDIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PRISTINE=${1:-/data/illia/nearproof-deps/pq-e2e-pristine}
DEPS=${2:-/data/illia/nearproof-deps/pq-e2e-d}
OUTDIR=${3:-$HERE/patches}
E2E_FILES="stark-backend-unified/crates/stark-backend/src/verifier/mod.rs
openvm-sha384/crates/recursion/src/nv/circuit.rs
openvm-sha384/crates/recursion/src/nv/verifier.rs
openvm-sha384/crates/recursion/src/nv/vd.rs
openvm-sha384/crates/recursion/src/nv/tests.rs"
ZK_FILES="stark-backend-unified/crates/stark-backend/src/config.rs
stark-backend-unified/crates/stark-backend/src/proof.rs
stark-backend-unified/crates/stark-backend/src/prover/stacked_pcs.rs
stark-backend-unified/crates/stark-backend/src/verifier/proof_shape.rs
stark-backend-unified/crates/stark-backend/src/verifier/mod.rs
stark-backend-unified/crates/stark-backend/tests/stream_commit.rs
stark-backend-unified/crates/cpu-backend/src/device.rs
openvm-sha384/crates/recursion/src/sha384/e2e_tests.rs"
T=$(mktemp -d /data/illia/nearproof-deps/.mkpatch.XXXX); trap 'rm -rf "$T"' EXIT
# stage 1: the e2e overlay is stored in-tree as the e2e-verify patch only when E2E_REFRESH=1
if [ "${E2E_REFRESH:-0}" = 1 ]; then
  : > "$OUTDIR/e2e-verify.patch"
  for f in $E2E_FILES; do
    (cd / && diff -u --label "a/$f" --label "b/$f" "$PRISTINE/$f" "$DEPS/$f") >> "$OUTDIR/e2e-verify.patch" || true
  done
fi
# stage 2: PRISTINE + e2e-verify.patch, restricted to the zk files, then diff to the live tree
for f in $E2E_FILES $ZK_FILES; do mkdir -p "$T/b/$(dirname "$f")"; cp "$PRISTINE/$f" "$T/b/$f"; done
(cd "$T/b" && patch -s -p1 --no-backup-if-mismatch < "$OUTDIR/e2e-verify.patch")
: > "$OUTDIR/zk-pcs.patch"
for f in $ZK_FILES; do
  (cd / && diff -u --label "a/$f" --label "b/$f" "$T/b/$f" "$DEPS/$f") >> "$OUTDIR/zk-pcs.patch" || true
done
sha256sum "$OUTDIR/e2e-verify.patch" "$OUTDIR/zk-pcs.patch"
