#!/usr/bin/env bash
# Build recipe for the zkvm-sp1 candidate. Run by the judge as
# `bash build-recipe/build.sh` from the package root, OFFLINE, with a fresh
# $HOME and SOURCE_DATE_EPOCH=0. Two independent builds must produce
# bit-identical out/{prepare,prove,verify}.
#
# Toolchains required in the build image (NOT shipped in the package):
#   * Rust 1.96.0 (host; source/rust-toolchain.toml)
#   * the SP1 `succinct` Rust toolchain for riscv64im-succinct-zkvm-elf
#     (sp1up / cargo-prove v6.8.1, rustc 1.96.0-dev), found via $SP1_RUSTC or
#     `rustup run succinct`.  If it is absent the build FALLS BACK to the
#     shipped guest ELF (source/guest-elf/transfer-guest.elf), which must match
#     the digest pinned in dependency-locks/guest-elf.sha256; the build prints
#     GUEST-NOT-REBUILT and writes out/guest-provenance.txt accordingly.  In that
#     case BUILD_REPRODUCIBLE does not cover the guest program (EVIDENCE.md).
set -euo pipefail

ROOT="$(pwd)"
export CARGO_HOME="${HOME}/cargo-home"
export CARGO_NET_OFFLINE=true
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
export TZ=UTC LC_ALL=C
REMAP="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo"

cd "${ROOT}/source"
for v in vendor vendor-guest; do
  [ -d "$v" ] || { echo "source/$v missing: run build-recipe/vendor.sh before packing" >&2; exit 1; }
done
cmp -s Cargo.lock ../dependency-locks/Cargo.lock \
  || { echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2; exit 1; }
cmp -s guest/Cargo.lock ../dependency-locks/guest-Cargo.lock \
  || { echo "dependency-locks/guest-Cargo.lock differs from source/guest/Cargo.lock" >&2; exit 1; }
PIN="$(cut -d' ' -f1 ../dependency-locks/guest-elf.sha256)"

# ---------------------------------------------------------------- guest ELF
SP1_RUSTC="${SP1_RUSTC:-}"
if [ -z "${SP1_RUSTC}" ] && command -v rustup >/dev/null 2>&1; then
  if SYSROOT="$(rustup run succinct rustc --print sysroot 2>/dev/null)"; then
    SP1_RUSTC="${SYSROOT}/bin/rustc"
  fi
fi
mkdir -p guest-elf "${ROOT}/out"
if [ -n "${SP1_RUSTC}" ] && [ -x "${SP1_RUSTC}" ]; then
  # Same flags as sp1-build 6.8.1 (crates/build/src/command/utils.rs), plus path remapping.
  FLAGS=(-C passes=lower-atomic -C link-arg=--image-base=2013265920 -C panic=abort
         --cfg 'getrandom_backend="custom"'
         -C llvm-args=-misched-prera-direction=bottomup -C llvm-args=-misched-postra-direction=bottomup
         --remap-path-prefix="${ROOT}=/candidate" --remap-path-prefix="${CARGO_HOME}=/cargo"
         -C strip=symbols)
  ENC="$(IFS=$'\x1f'; echo "${FLAGS[*]}")"
  ( cd guest && env -u RUSTFLAGS RUSTC="${SP1_RUSTC}" RUSTC_BOOTSTRAP=1 \
      CARGO_TARGET_DIR="${ROOT}/source/target/guest" CARGO_ENCODED_RUSTFLAGS="${ENC}" \
      cargo build --release --locked --offline --target riscv64im-succinct-zkvm-elf )
  cp target/guest/riscv64im-succinct-zkvm-elf/release/transfer-guest guest-elf/transfer-guest.elf
  GOT="$(sha256sum guest-elf/transfer-guest.elf | cut -d' ' -f1)"
  if [ "${GOT}" != "${PIN}" ]; then
    echo "rebuilt guest ELF sha256 ${GOT} != pinned ${PIN} (dependency-locks/guest-elf.sha256)" >&2
    exit 1
  fi
  echo "guest ELF rebuilt from source: sha256 ${GOT} ($("${SP1_RUSTC}" --version))" > "${ROOT}/out/guest-provenance.txt"
else
  [ -f guest-elf/transfer-guest.elf ] || { echo "no succinct toolchain and no shipped guest ELF" >&2; exit 1; }
  GOT="$(sha256sum guest-elf/transfer-guest.elf | cut -d' ' -f1)"
  [ "${GOT}" = "${PIN}" ] || { echo "shipped guest ELF does not match pinned digest" >&2; exit 1; }
  echo "GUEST-NOT-REBUILT: succinct toolchain unavailable; using shipped ELF sha256 ${GOT}" >&2
  echo "GUEST-NOT-REBUILT: shipped guest ELF sha256 ${GOT}" > "${ROOT}/out/guest-provenance.txt"
fi

# ---------------------------------------------------------------- host binaries
# CARGO_BUILD_RUSTFLAGS (not RUSTFLAGS) so that the nested cargo build of
# sp1-core-executor-runner-binary (done by sp1-core-executor-runner's build.rs,
# which clears RUSTFLAGS) is path-remapped too.
env -u RUSTFLAGS CARGO_BUILD_RUSTFLAGS="${REMAP} -C strip=symbols" \
  NEARPROOF_HOST_MANIFEST="${ROOT}/source/Cargo.toml" \
  CARGO_TARGET_DIR="${ROOT}/source/target/host" \
  cargo build --release --locked --offline -p zk-prover -p zk-verifier --bins

for bin in prepare prove verify; do
  install -m 0755 "target/host/release/${bin}" "${ROOT}/out/${bin}"
done
sha256sum "${ROOT}"/out/{prepare,prove,verify} | sed "s#${ROOT}/##"
