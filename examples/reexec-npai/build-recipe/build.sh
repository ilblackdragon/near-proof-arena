#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
#
#   out/verifier.npai  — THE VERIFIER: the NPAI v1 image `encode program` of the
#                        Lean definition ReexecNpai.program (formal/), written by
#                        source/export/Export.lean. The arena runs its own
#                        interpreter on this exact file (verify_route npai-v1);
#                        the certificate pins its SHA-256.
#   out/prepare, out/prove — Rust prover (source/), vendored crates.
#   out/verify         — local convenience wrapper only (a verbatim copy of the
#                        judge's interpreter with the image embedded); the arena
#                        does not run it on this route.
set -euo pipefail

ROOT="$(pwd)"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
mkdir -p out

# ---- Lean: elaborate the program definition and export the image ------------
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
( cd source/lean-vendor && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256" >&2
  exit 1
}
( cd source/verifier && lake build ReexecNpaiProgram >&2 && \
  lake env lean --run ../export/Export.lean "${ROOT}/out/verifier.npai" )

# ---- Rust -------------------------------------------------------------------
export CARGO_HOME="${HOME}/cargo-home"
export CARGO_TARGET_DIR="${ROOT}/source/target"
export CARGO_NET_OFFLINE=true
export RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo -C strip=symbols"
cmp -s source/Cargo.lock dependency-locks/Cargo.lock || {
  echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2
  exit 1
}
export NPAI_IMAGE="${ROOT}/out/verifier.npai"
( cd source && cargo build --release --locked --offline --bin prepare --bin prove --bin verify )
for bin in prepare prove verify; do
  install -m 0755 "source/target/release/${bin}" "out/${bin}"
done
