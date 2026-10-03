#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
#
#   out/prepare, out/prove  — Rust (source/), vendored crates, --locked --offline
#   out/verify              — the Lean verifier model ReexecWitness.Model.verifier
#                             compiled by the Lean compiler, laid out exactly like
#                             the judge's native-lean build (runners/formal-checker
#                             `native_build`): trusted sources + the model's import
#                             closure under src/, the judge-owned main wrapper,
#                             one lakefile with no requires.
set -euo pipefail

ROOT="$(pwd)"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"

# ---- Rust prover ------------------------------------------------------------
export CARGO_HOME="${HOME}/cargo-home"
export CARGO_TARGET_DIR="${ROOT}/source/target"
export CARGO_NET_OFFLINE=true
export RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo -C strip=symbols"
cmp -s source/Cargo.lock dependency-locks/Cargo.lock || {
  echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2
  exit 1
}
( cd source && cargo build --release --locked --offline --bin prepare --bin prove )
mkdir -p out
for bin in prepare prove; do
  install -m 0755 "source/target/release/${bin}" "out/${bin}"
done

# ---- Lean verifier (native-lean route layout) -------------------------------
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
( cd source/lean-vendor && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256" >&2
  exit 1
}
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/src/ReexecWitness"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/src/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/src/"
# the model's import closure inside formal/
for m in ProofCodec Model; do cp "formal/ReexecWitness/${m}.lean" "${NB}/src/ReexecWitness/"; done
cp source/verifier/Main.lean "${NB}/src/ArenaVerifyMain.lean"
roots=$(cd "${NB}/src" && find . -name '*.lean' ! -name ArenaVerifyMain.lean | sed 's|^\./||; s|\.lean$||; s|/|.|g' | LC_ALL=C sort | sed 's/.*/"&"/' | paste -sd, - | sed 's/,/, /g')
cat > "${NB}/lakefile.toml" <<TOML
name = "arenaverify"
srcDir = "src"

[[lean_lib]]
name = "ArenaVerifyLib"
roots = [${roots}]

[[lean_exe]]
name = "verify"
root = "ArenaVerifyMain"
TOML
cp source/verifier/lean-toolchain "${NB}/lean-toolchain"
( cd "${NB}" && lake build verify )
install -m 0755 "${NB}/.lake/build/bin/verify" out/verify
rm -rf "${NB}"
