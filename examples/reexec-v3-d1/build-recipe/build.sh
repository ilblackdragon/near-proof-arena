#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
#
#   out/prepare             — Rust (source/), std only, --locked --offline
#   out/prove               — Lean: source/prover/ProveMain.lean (the verifier model's own
#                             normaliser ReexecV3D1.normSW) linked with the same objects
#   out/verify              — the Lean verifier model ReexecV3D1.Model.verifier
#                             compiled by the Lean compiler, laid out exactly like
#                             the judge's native-lean build (runners/formal-checker
#                             `native_build`): every trusted module of challenge
#                             near-chunk-validation-d0 (ArenaCore, NearSpec,
#                             NearSpecV3; runners/formal-checker/challenges/
#                             near-chunk-validation-d0.json) + the model's import
#                             closure, the judge-owned main wrapper, one link.
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
( cd source && cargo build --release --locked --offline --bin prepare --bin leanorder )
mkdir -p out
for bin in prepare; do
  install -m 0755 "source/target/release/${bin}" "out/${bin}"
done

# ---- Lean verifier: the judge's native-lean build, replicated --------------
# runners/formal-checker `native_build`: `lean -c` every trusted module (judge
# topo order over the union of the trusted packages) and the model's import
# closure, the judge-owned main wrapper (`ARENACORE_MAIN_TEMPLATE`, verbatim in
# source/verifier/), then `leanc -c -O3 -DNDEBUG` per C file and one `leanc -o`
# link in that order. Object files and the link are path-independent, so
# out/verify is byte-identical to the judge's build of ReexecV3D1.Model.verifier.
export PATH="${ELAN_HOME:-${HOME}/.elan}/bin:${PATH}"
( cd source/lean-vendor && find . -type f ! -path '*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  | cmp -s - dependency-locks/lean-vendor.sha256 || {
  echo "source/lean-vendor differs from dependency-locks/lean-vendor.sha256" >&2
  exit 1
}
TC="$(cd source/verifier && lean --print-prefix)"
LEAN="${TC}/bin/lean"
LEANC="${TC}/bin/leanc"
ORDER="${ROOT}/source/target/release/leanorder"
TRUSTED_PREFIXES="ArenaCore NearSpec.Bytes NearSpec.SHA256 NearSpec.AccountId NearSpec.Primitives NearSpec.Trie NearSpec.Outcome NearSpec.TransferV1 NearSpec.ClaimCodec NearSpec.Challenge NearSpec.TrieUpsert NearSpec.Bandwidth NearSpecV3.ChaCha20 NearSpecV3.GF256 NearSpecV3.ReedSolomon NearSpecV3.F64 NearSpecV3.Congestion NearSpecV3.BandwidthScheduler NearSpecV3.Wire NearSpecV3.ClaimV3 NearSpecV3.ClaimV3Props NearSpecV3.WitnessV3 NearSpecV3.Layout NearSpecV3.TrieBuild NearSpecV3.RuntimeD0 NearSpecV3.ChunkValidationV0 NearSpecV3.ChallengeV3"
MODEL_MODULES="ReexecV3D1.CanonDefs ReexecV3D1.NormDefs ReexecV3D1.KeysD0 ReexecV3D1.NormalDefs ReexecV3D1.NormBytesDefs ReexecV3D1.Model"   # the model's import closure in formal/
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/tsrc" "${NB}/msrc/ReexecV3D1" "${NB}/main" "${NB}/olean" "${NB}/c" "${NB}/o"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/v3/NearSpecV3 "${NB}/tsrc/"
for m in ${MODEL_MODULES}; do cp "formal/${m//.//}.lean" "${NB}/msrc/${m//.//}.lean"; done
sed -e 's/{{model_module}}/ReexecV3D1.Model/' -e 's/{{model_decl}}/ReexecV3D1.Model.verifier/' \
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
# model modules in the judge's order: its topological order of the WHOLE formal tree,
# restricted to the model closure
mkdir -p "${NB}/fsrc"
cp -R formal/ReexecV3D1 "${NB}/fsrc/"
for m in $("${ORDER}" "${NB}/fsrc" ReexecV3D1); do
  case " ${MODEL_MODULES} " in *" ${m} "*) compile "${NB}/msrc" "$m"; LINK+=("$m");; esac
done
compile "${NB}/main" ArenaVerifyMain; LINK+=(ArenaVerifyMain)
objs=()
for m in "${LINK[@]}"; do
  "${LEANC}" -c -O3 -DNDEBUG "${NB}/c/${m}.c" -o "${NB}/o/${m}.o"
  objs+=("${NB}/o/${m}.o")
done
"${LEANC}" -o "${NB}/o/verify" "${objs[@]}"
install -m 0755 "${NB}/o/verify" out/verify
# out/prove: the same trusted + model objects, the prover's main instead of the judge's
mkdir -p "${NB}/prover"
cp source/prover/ProveMain.lean "${NB}/prover/ProveMain.lean"
compile "${NB}/prover" ProveMain
"${LEANC}" -c -O3 -DNDEBUG "${NB}/c/ProveMain.c" -o "${NB}/o/ProveMain.o"
pobjs=("${objs[@]:0:${#objs[@]}-1}" "${NB}/o/ProveMain.o")
"${LEANC}" -o "${NB}/o/prove" "${pobjs[@]}"
install -m 0755 "${NB}/o/prove" out/prove
rm -rf "${NB}"
