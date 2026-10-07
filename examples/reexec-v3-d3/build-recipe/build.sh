#!/usr/bin/env bash
# Offline, reproducible build (run by the judge as `bash build-recipe/build.sh`
# from the package root, no network, fresh $HOME, SOURCE_DATE_EPOCH=0).
#
#   out/prepare             — Rust (source/), std only, --locked --offline
#   out/prove               — Lean: source/prover/ProveMain.lean (the verifier model's own
#                             normaliser ReexecV3D3.Read.canonW) linked with the same objects
#   out/verify              — the Lean verifier model ReexecV3D3.Model.verifier
#                             compiled by the Lean compiler, laid out exactly like
#                             the judge's native-lean build (runners/formal-checker
#                             `native_build`): every trusted module of challenge
#                             near-chunk-v3 (ArenaCore, NearSpec,
#                             NearSpecV3; runners/formal-checker/challenges/
#                             near-chunk-v3.json) + the model's import
#                             closure, the judge-owned main wrapper, one link.
set -euo pipefail

ROOT="$(pwd)"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-0}"
export LEAN_NUM_THREADS=2
export CARGO_BUILD_JOBS=2

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
# out/verify is byte-identical to the judge's build of ReexecV3D3.Model.verifier.
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
TRUSTED_PREFIXES="ArenaCore NearSpec.Bytes NearSpec.SHA256 NearSpec.Trie NearSpec.AccountId NearSpec.Primitives NearSpec.Outcome NearSpec.TransferV1 NearSpec.ClaimCodec NearSpec.Challenge NearSpec.TrieUpsert NearSpec.Bandwidth NearSpecV3.Wire NearSpecV3.ClaimV3 NearSpecV3.WitnessV3 NearSpecV3.Layout NearSpecV3.TrieBuild NearSpecV3.RuntimeD0 NearSpecV3.ChaCha20 NearSpecV3.F64 NearSpecV3.Congestion NearSpecV3.BandwidthScheduler NearSpecV3.GF256 NearSpecV3.ReedSolomon NearSpecV3.ChunkValidationV0 NearSpecV3.ClaimV3Props NearSpecV3.ChallengeV3 NearSpecV3.SHA512 NearSpecV3.Ed25519 NearSpecV3.TxD1 NearSpecV3.RuntimeD1 NearSpecV3.ChunkValidationD1 NearSpecV3.D2.Trie NearSpecV3.D2.Types NearSpecV3.D2.Fees NearSpecV3.D2.State NearSpecV3.D2.Queues NearSpecV3.D2.Actions NearSpecV3.D2.Receipts NearSpecV3.D2.TxD2 NearSpecV3.D2.Validators NearSpecV3.D2.RuntimeD2 NearSpecV3.ChunkValidationD2 NearSpecV3.Wasm.Syntax NearSpecV3.Wasm.Decode NearSpecV3.Wasm.Validate NearSpecV3.Wasm.FiniteWasm NearSpecV3.Wasm.HostSigs NearSpecV3.Wasm.InstrSize NearSpecV3.Wasm.Prepare NearSpecV3.Wasm.Numerics NearSpecV3.Wasm.Crypto NearSpecV3.Wasm.TrieStore NearSpecV3.Wasm.Machine NearSpecV3.Wasm.TrieAccounting NearSpecV3.Wasm.Host NearSpecV3.Wasm.Exec NearSpecV3.D3.FunctionCall NearSpecV3.ChallengeChunkV3"
MODEL_MODULES="ReexecV3D3.CanonDefs ReexecV3D3.NormDefs ReexecV3D3.Canon ReexecV3D3.Logged.Store ReexecV3D3.Logged.TrieDec ReexecV3D3.Logged.TrieHash ReexecV3D3.Logged.LazyTrie ReexecV3D3.Logged.LazyTrieSpec ReexecV3D3.Logged.LazyFinalize ReexecV3D3.Logged.LM ReexecV3D3.Logged.D2State ReexecV3D3.Logged.D2Queues ReexecV3D3.Logged.Runtime.D2Actions ReexecV3D3.Logged.Runtime.D2Receipts ReexecV3D3.Logged.Runtime.D2Runtime ReexecV3D3.Logged.Runtime.D2Check ReexecV3D3.Logged.Runtime.WasmStep ReexecV3D3.Logged.WasmStore ReexecV3D3.Logged.WasmHostL ReexecV3D3.Logged.Runtime.Dr ReexecV3D3.Logged.Runtime.WasmRun ReexecV3D3.Logged.D3L ReexecV3D3.Logged.Runtime.D3Check ReexecV3D3.Logged.Runtime.API ReexecV3D3.ReadCanonDefs ReexecV3D3.Model"   # the model's import closure in formal/
NB="${ROOT}/build-native"
rm -rf "${NB}"
mkdir -p "${NB}/tsrc" "${NB}/msrc/ReexecV3D3" "${NB}/main" "${NB}/olean" "${NB}/c" "${NB}/o"
cp -R source/lean-vendor/formal-core/ArenaCore source/lean-vendor/formal-core/ArenaCore.lean "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/NearSpec "${NB}/tsrc/"
cp -R source/lean-vendor/spec/lean/v3/NearSpecV3 "${NB}/tsrc/"
for m in ${MODEL_MODULES}; do
  mkdir -p "$(dirname "${NB}/msrc/${m//.//}.lean")"
  cp "formal/${m//.//}.lean" "${NB}/msrc/${m//.//}.lean"
done
sed -e 's/{{model_module}}/ReexecV3D3.Model/' -e 's/{{model_decl}}/ReexecV3D3.Model.verifier/' \
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
cp -R formal/ReexecV3D3 "${NB}/fsrc/"
for m in $("${ORDER}" "${NB}/fsrc" ReexecV3D3); do
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
