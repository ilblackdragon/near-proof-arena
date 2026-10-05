#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
# Two builds must be bit-identical.
#
#   out/prepare, out/prove  Rust (source/), every crate from source/vendor/
#                           (build-recipe/vendor.sh: crates.io + Plonky3 @
#                           3acc8b7), --locked --offline.
#   out/verify              the Lean verifier model [formal] verifier_model
#                           compiled by the Lean compiler, laid out exactly like
#                           the judge's native-lean build (runners/formal-checker
#                           `native_build`): trusted sources (source/lean-vendor)
#                           + the model's import closure in formal/ (which
#                           includes the vendored zk-formal package
#                           formal/ZkFormal), the judge-owned main wrapper, one
#                           link with no Lake.
#
# Toolchains required in the build image (not shipped): Rust 1.96.0
# (source/rust-toolchain.toml), Lean leanprover/lean4:v4.34.1 (elan).
#
# Rust codegen is pinned to x86-64-v3 (AVX2/BMI2/FMA) + SHA-NI + AES-NI (the
# challenge hardware profile is an AMD Zen 5 host); the binaries do not depend
# on the build host's CPU.
#
# Overrides (developer use; the judge sets none): MODEL_MODULE, MODEL_DECL
# (default: [formal] verifier_model_module / verifier_model of candidate.toml),
# SKIP_LEAN=1 (Rust only).
set -euo pipefail

ROOT="$(pwd)"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
export TZ=UTC LC_ALL=C

# ---- Rust prover ------------------------------------------------------------
# Source replacement lives in the (fresh) CARGO_HOME, not in source/.cargo, so
# that development builds in source/ keep resolving from the network.
export CARGO_HOME="${HOME}/cargo-home"
export CARGO_NET_OFFLINE=true
[ -d source/vendor ] || { echo "source/vendor missing: run build-recipe/vendor.sh before packing" >&2; exit 1; }
cmp -s source/Cargo.lock dependency-locks/Cargo.lock || {
  echo "dependency-locks/Cargo.lock differs from source/Cargo.lock" >&2
  exit 1
}
mkdir -p "${CARGO_HOME}"
cat > "${CARGO_HOME}/config.toml" <<EOF
[source.crates-io]
replace-with = "vendored-sources"

[source."git+https://github.com/Plonky3/Plonky3?rev=3acc8b70e68d6c2afc03930700c26540bd47458d"]
git = "https://github.com/Plonky3/Plonky3"
rev = "3acc8b70e68d6c2afc03930700c26540bd47458d"
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "${ROOT}/source/vendor"

[net]
offline = true
EOF
# cargo_build <target-cpu> <target-dir> <cargo args...>
cargo_build() {
  local cpu="$1" dir="$2"
  shift 2
  ( cd source && env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
      CARGO_BUILD_RUSTFLAGS="--remap-path-prefix=${ROOT}=/candidate --remap-path-prefix=${CARGO_HOME}=/cargo -C strip=symbols -C target-cpu=${cpu} -C target-feature=+sha,+aes" \
      CARGO_TARGET_DIR="${ROOT}/source/${dir}" \
      cargo build --release --locked --offline "$@" )
}
cargo_build x86-64-v3 target --bin prepare --bin prove --bin leanorder
# Same prover source for AVX-512 CPUs; out/prove switches to it at run time
# (runtime CPU detection, src/bin/prove.rs) — identical proof bytes.
cargo_build x86-64-v4 target-avx512 --bin prove
mkdir -p out
for bin in prepare prove; do
  install -m 0755 "source/target/release/${bin}" "out/${bin}"
done
install -m 0755 source/target-avx512/release/prove out/prove-avx512
[ "${SKIP_LEAN:-0}" = 1 ] && { sha256sum out/prepare out/prove out/prove-avx512; exit 0; }

# ---- Lean verifier: the judge's native-lean build, replicated --------------
# runners/formal-checker `native_build`: `lean -c` every trusted module (judge
# `topo` order) and the model's import closure (staged-tree topological order,
# filtered to the closure), the judge-owned main wrapper (`ARENACORE_MAIN_
# TEMPLATE`, verbatim in source/verifier/), then `leanc -c -O3 -DNDEBUG` per C
# file and one `leanc -o` link in that order. Object files and the link are
# path-independent, so out/verify is byte-identical to the judge's build.
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
toml() { sed -n "s/^${1}[[:space:]]*=[[:space:]]*\"\\([^\"]*\\)\".*/\\1/p" candidate.toml; }
MODEL_MODULE="${MODEL_MODULE:-$(toml verifier_model_module)}"
MODEL_DECL="${MODEL_DECL:-$(toml verifier_model)}"
[ -n "${MODEL_MODULE}" ] && [ -n "${MODEL_DECL}" ] || { echo "candidate.toml: no [formal] verifier_model(_module)" >&2; exit 1; }
( cd source/lean-vendor && find . -type f ! -path './*/.lake/*' | sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256 (build-recipe/sync-lean.sh)" >&2
  exit 1
}
( cd formal && find ZkFormal -type f -name '*.lean' 2>/dev/null | sort | xargs -r sha256sum ) \
  | cmp -s - dependency-locks/zk-formal.sha256 || {
  echo "formal/ZkFormal differs from dependency-locks/zk-formal.sha256 (build-recipe/sync-lean.sh)" >&2
  exit 1
}
TC="$(cd source/verifier && lean --print-prefix)"
LEAN="${TC}/bin/lean"
LEANC="${TC}/bin/leanc"
ORDER="${ROOT}/source/target/release/leanorder"
# runners/formal-checker/challenges/near-transfer-receipt-v1.json `trusted`.
TRUSTED_PREFIXES="ArenaCore NearSpec.Bytes NearSpec.SHA256 NearSpec.AccountId NearSpec.Primitives NearSpec.Trie NearSpec.Outcome NearSpec.TransferV1 NearSpec.ClaimCodec NearSpec.Challenge"
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/tsrc" "${NB}/msrc" "${NB}/main" "${NB}/olean" "${NB}/c" "${NB}/o"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/tsrc/"
TRUSTED="$("${ORDER}" "${NB}/tsrc" ${TRUSTED_PREFIXES})"
MODEL="$("${ORDER}" --closure formal "${MODEL_MODULE}" --trusted "${NB}/tsrc" ${TRUSTED_PREFIXES})"
for m in ${MODEL}; do
  mkdir -p "$(dirname "${NB}/msrc/${m//.//}")"
  cp "formal/${m//.//}.lean" "${NB}/msrc/${m//.//}.lean"
done
sed -e "s/{{model_module}}/${MODEL_MODULE}/" -e "s/{{model_decl}}/${MODEL_DECL}/" \
  source/verifier/ArenaVerifyMain.lean.template > "${NB}/main/ArenaVerifyMain.lean"
export LEAN_PATH="${NB}/olean"
compile() {  # root module
  local root="$1" m="$2" stem="${2//.//}"
  mkdir -p "$(dirname "${NB}/olean/${stem}")"
  "${LEAN}" -R "${root}" -o "${NB}/olean/${stem}.olean" -i "${NB}/olean/${stem}.ilean" \
    -c "${NB}/c/${m}.c" "${root}/${stem}.lean"
}
LINK=()
for m in ${TRUSTED}; do compile "${NB}/tsrc" "$m"; LINK+=("$m"); done
for m in ${MODEL}; do compile "${NB}/msrc" "$m"; LINK+=("$m"); done
compile "${NB}/main" ArenaVerifyMain; LINK+=(ArenaVerifyMain)
objs=()
for m in "${LINK[@]}"; do
  "${LEANC}" -c -O3 -DNDEBUG "${NB}/c/${m}.c" -o "${NB}/o/${m}.o"
  objs+=("${NB}/o/${m}.o")
done
"${LEANC}" -o "${NB}/o/verify" "${objs[@]}"
install -m 0755 "${NB}/o/verify" out/verify
rm -rf "${NB}"
sha256sum out/prepare out/prove out/prove-avx512 out/verify
