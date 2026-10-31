#!/usr/bin/env bash
# Regenerate patches/e2e-verify.patch: the e2e overlay (tape-eval statement, verifier reuse) on
# top of the pinned cpu-fast deps. PRISTINE = a fresh setup_cpu_fast_deps.sh tree, DEPS = the
# e2e tree. Applied by setup_e2e.sh with `patch -p1` from the deps root.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PRISTINE=${1:-/data/illia/nearproof-deps/pq-e2e-pristine}
DEPS=${2:-/data/illia/nearproof-deps/pq-e2e-zk}
OUT=${3:-$HERE/../patches/e2e-verify.patch}
mkdir -p "$(dirname "$OUT")"
: > "$OUT"
for f in \
  stark-backend-unified/crates/stark-backend/src/verifier/mod.rs \
  openvm-sha384/crates/recursion/src/nv/circuit.rs \
  openvm-sha384/crates/recursion/src/nv/verifier.rs \
  openvm-sha384/crates/recursion/src/nv/vd.rs \
  openvm-sha384/crates/recursion/src/nv/tests.rs; do
  (cd / && diff -u --label "a/$f" --label "b/$f" "$PRISTINE/$f" "$DEPS/$f") >> "$OUT" || true
done
sha256sum "$OUT"
