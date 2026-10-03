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

# ---- Lean verifier: the judge's native-lean build, replicated --------------
# runners/formal-checker `native_build`: `lean -c` every trusted module (judge
# topo order) and the model's import closure, the judge-owned main wrapper
# (`ARENACORE_MAIN_TEMPLATE`, verbatim in source/verifier/), then
# `leanc -c -O3 -DNDEBUG` per C file and one `leanc -o` link in that order.
# Object files and the link are path-independent, so out/verify is
# byte-identical to the judge's build of ReexecWitness.Model.verifier.
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
( cd source/lean-vendor && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256" >&2
  exit 1
}
TC="$(cd source/verifier && lean --print-prefix)"
LEAN="${TC}/bin/lean"
LEANC="${TC}/bin/leanc"
( cd source && cargo build --release --locked --offline --bin leanorder )
ORDER="${ROOT}/source/target/release/leanorder"
TRUSTED_PREFIXES="ArenaCore NearSpec.Bytes NearSpec.SHA256 NearSpec.AccountId NearSpec.Primitives NearSpec.Trie NearSpec.Outcome NearSpec.TransferV1 NearSpec.ClaimCodec NearSpec.Challenge"
MODEL_MODULES="ReexecWitness.ProofCodec ReexecWitness.Model"   # the model's import closure in formal/
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/tsrc" "${NB}/msrc/ReexecWitness" "${NB}/main" "${NB}/olean" "${NB}/c" "${NB}/o"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/tsrc/"
for m in ${MODEL_MODULES}; do cp "formal/${m//.//}.lean" "${NB}/msrc/${m//.//}.lean"; done
sed -e 's/{{model_module}}/ReexecWitness.Model/' -e 's/{{model_decl}}/ReexecWitness.Model.verifier/' \
  source/verifier/ArenaVerifyMain.lean.template > "${NB}/main/ArenaVerifyMain.lean"
export LEAN_PATH="${NB}/olean"
compile() {  # root module
  local root="$1" m="$2" stem="${2//.//}"
  mkdir -p "$(dirname "${NB}/olean/${stem}")"
  "${LEAN}" -R "${root}" -o "${NB}/olean/${stem}.olean" -i "${NB}/olean/${stem}.ilean" \
    -c "${NB}/c/${m}.c" "${root}/${stem}.lean"
}
LINK=()
for m in $("${ORDER}" "${NB}/tsrc" ${TRUSTED_PREFIXES}); do compile "${NB}/tsrc" "$m"; LINK+=("$m"); done
for m in $("${ORDER}" "${NB}/msrc" ReexecWitness); do compile "${NB}/msrc" "$m"; LINK+=("$m"); done
compile "${NB}/main" ArenaVerifyMain; LINK+=(ArenaVerifyMain)
objs=()
for m in "${LINK[@]}"; do
  "${LEANC}" -c -O3 -DNDEBUG "${NB}/c/${m}.c" -o "${NB}/o/${m}.o"
  objs+=("${NB}/o/${m}.o")
done
"${LEANC}" -o "${NB}/o/verify" "${objs[@]}"
install -m 0755 "${NB}/o/verify" out/verify
rm -rf "${NB}"
