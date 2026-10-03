#!/usr/bin/env bash
# Build recipe for stark-plonky3. Run by the judge as `bash build-recipe/build.sh`
# from the package root, OFFLINE, with a fresh $HOME and SOURCE_DATE_EPOCH=0.
# Produces out/{prepare,prove,verify}; two builds must be bit-identical.
#
# Toolchain required in the build image (not shipped): Rust 1.96.0
# (source/rust-toolchain.toml). Every crate comes from source/vendor/
# (build-recipe/vendor.sh), checked against Cargo.lock.
#
# Codegen target is pinned to x86-64-v3 (AVX2/BMI2/FMA) + SHA-NI + AES-NI
# (the challenge hardware profile is an AMD Zen 5 host); the binaries do not
# depend on the build host's CPU.
set -euo pipefail

ROOT="$(pwd)"
export CARGO_HOME="${HOME}/cargo-home"
export CARGO_NET_OFFLINE=true
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
export TZ=UTC LC_ALL=C
cd "${ROOT}/source"
[ -d vendor ] || { echo "source/vendor missing: run build-recipe/vendor.sh before packing" >&2; exit 1; }
cmp -s Cargo.lock ../dependency-locks/Cargo.lock \
  || { echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2; exit 1; }
env -u RUSTFLAGS \
  CARGO_BUILD_RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo -C strip=symbols -C target-cpu=x86-64-v3 -C target-feature=+sha,+aes" \
  CARGO_TARGET_DIR="${ROOT}/source/target" \
  cargo build --release --locked --offline --bin prepare --bin prove --bin verify
mkdir -p "${ROOT}/out"
for bin in prepare prove verify; do
  install -m 0755 "target/release/${bin}" "${ROOT}/out/${bin}"
done
sha256sum "${ROOT}"/out/{prepare,prove,verify} | sed "s#${ROOT}/##"
