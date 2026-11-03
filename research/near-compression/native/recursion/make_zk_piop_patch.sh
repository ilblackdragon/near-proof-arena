#!/usr/bin/env bash
# Regenerate patches/zk-piop.patch (lane E2E-D, 2026-11-03: PIOP masking, `WhirLevers::zk >= 4`)
#   = PRISTINE + e2e-verify.patch + zk-pcs.patch  ->  DEPS   over PIOP_FILES
# PRISTINE = a fresh setup_cpu_fast_deps.sh tree, DEPS = the live e2e tree. Applied by
# setup_e2e_verify_deps.sh after zk-pcs.patch (E2E_ZK=1). Construction and argument:
# research/near-compression/e2e/ZK-ARGUMENT.md.
# usage: make_zk_piop_patch.sh [PRISTINE] [DEPS] [OUTDIR]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PRISTINE=${1:-/data/illia/nearproof-deps/pq-e2e-pristine}
DEPS=${2:-/data/illia/nearproof-deps/pq-e2e-d}
OUTDIR=${3:-$HERE/patches}
SB=stark-backend-unified/crates
PIOP_FILES="$SB/stark-backend/src/zk.rs
$SB/stark-backend/src/lib.rs
$SB/stark-backend/src/config.rs
$SB/stark-backend/src/proof.rs
$SB/stark-backend/src/prover/stacked_pcs.rs
$SB/stark-backend/src/prover/stacked_reduction.rs
$SB/stark-backend/src/prover/logup_zerocheck/mod.rs
$SB/stark-backend/src/soundness/calculator.rs
$SB/stark-backend/src/verifier/mod.rs
$SB/stark-backend/src/verifier/proof_shape.rs
$SB/stark-backend/src/verifier/batch_constraints.rs
$SB/stark-backend/src/verifier/fractional_sumcheck_gkr.rs
$SB/stark-backend/src/verifier/stacked_reduction.rs
$SB/cpu-backend/src/device.rs
$SB/cpu-backend/src/fast/gkr.rs
$SB/cpu-backend/src/logup_zerocheck/mod.rs
openvm-sha384/crates/recursion/src/batch_constraint/mod.rs
openvm-sha384/crates/recursion/src/gkr/mod.rs
openvm-sha384/crates/recursion/src/stacking/mod.rs"
T=$(mktemp -d /data/illia/nearproof-deps/.mkpatch.XXXX); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/b"
# every file the two earlier patches or this one touch, from PRISTINE (absent = new file)
for f in $(grep -h '^+++ b/' "$HERE/patches/e2e-verify.patch" "$HERE/patches/zk-pcs.patch" | sed 's|^+++ b/||') $PIOP_FILES; do
  [ -f "$PRISTINE/$f" ] || continue
  mkdir -p "$T/b/$(dirname "$f")"; cp "$PRISTINE/$f" "$T/b/$f"
done
(cd "$T/b" && patch -s -p1 --no-backup-if-mismatch < "$HERE/patches/e2e-verify.patch" \
  && patch -s -p1 --no-backup-if-mismatch < "$HERE/patches/zk-pcs.patch")
: > "$OUTDIR/zk-piop.patch"
for f in $PIOP_FILES; do
  src="$T/b/$f"; [ -f "$src" ] || src=/dev/null
  (cd / && diff -uN --label "a/$f" --label "b/$f" "$src" "$DEPS/$f") >> "$OUTDIR/zk-piop.patch" || true
done
sha256sum "$OUTDIR/zk-piop.patch"
