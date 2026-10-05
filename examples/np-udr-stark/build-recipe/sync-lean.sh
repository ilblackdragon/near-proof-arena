#!/usr/bin/env bash
# Packager step (NOT run by the judge; needs the repository checkout): copy
# the Lean sources the offline build compiles but that do not live in this
# package, and pin their digests in dependency-locks/.
#
#   source/lean-vendor/   JUDGE-TRUSTED packages, verbatim at the commit the
#                         challenge pins in toolchain_policy.allowed_packages
#                         (ArenaCore, NearSpec @ ${PIN}): formal-core's
#                         ArenaCore.lean + ArenaCore/**, and exactly the
#                         NearSpec modules runners/formal-checker/challenges/
#                         near-transfer-receipt-v1.json trusts. The judge
#                         supplies its own copies; these exist only so that
#                         build.sh can replicate its native-lean build offline.
#                         -> dependency-locks/lean-vendor.sha256
#   formal/ZkFormal{,.lean}  CANDIDATE code: the zk-formal Lake package
#                         (repo zk-formal/, lanes L1-L3). It is not trusted, so
#                         it cannot be a `require` (only ArenaCore/NearSpec are
#                         allowlisted) nor live in lean-vendor: the judge
#                         stages only formal/, and a model module may import
#                         only trusted modules, other formal/ modules and Init
#                         (pipeline.rs `native_build`). Hence it ships inside
#                         formal/ and is part of the verifier model's closure.
#                         -> dependency-locks/zk-formal.sha256
#
# usage: build-recipe/sync-lean.sh   (from anywhere)
set -euo pipefail
PIN=4f5c19dfbffe0fb14e48870ea9489f6e46a896f8   # challenge allowed_packages commit
pkg="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(git -C "$pkg" rev-parse --show-toplevel)"
NEARSPEC="Bytes SHA256 AccountId Primitives Trie Outcome TransferV1 ClaimCodec Challenge"

dst="$pkg/source/lean-vendor"
rm -rf "$dst"
mkdir -p "$dst/formal-core" "$dst/spec/lean"
git -C "$repo" archive "$PIN" formal-core/ArenaCore.lean formal-core/ArenaCore formal-core/lean-toolchain \
  | tar -xf - -C "$dst"
files=(spec/lean/lean-toolchain)
for m in $NEARSPEC; do files+=("spec/lean/NearSpec/$m.lean"); done
git -C "$repo" archive "$PIN" "${files[@]}" | tar -xf - -C "$dst"
cat > "$dst/formal-core/lakefile.toml" <<'TOML'
name = "ArenaCore"
version = "0.1.0"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[lean_lib]]
name = "ArenaCore"
TOML
cat > "$dst/spec/lean/lakefile.toml" <<'TOML'
name = "NearSpec"
version = "0.1.0"

[[lean_lib]]
name = "NearSpec"
globs = ["NearSpec.+"]

[[require]]
name = "ArenaCore"
path = "../../formal-core"
TOML
( cd "$dst" && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) \
  > "$pkg/dependency-locks/lean-vendor.sha256"

# zk-formal: the working tree (lanes commit there first), sources only.
rm -rf "$pkg/formal/ZkFormal" "$pkg/formal/ZkFormal.lean"
( cd "$repo/zk-formal" && git ls-files --cached --others --exclude-standard ZkFormal.lean 'ZkFormal/*.lean' 'ZkFormal/**/*.lean' \
  | LC_ALL=C sort -u | tar -cf - -T - ) | tar -xf - -C "$pkg/formal"
( cd "$pkg/formal" && find ZkFormal.lean ZkFormal -type f -name '*.lean' | LC_ALL=C sort | xargs sha256sum ) \
  > "$pkg/dependency-locks/zk-formal.sha256"
echo "lean-vendor: $(wc -l < "$pkg/dependency-locks/lean-vendor.sha256") files @ ${PIN:0:7}; zk-formal: $(wc -l < "$pkg/dependency-locks/zk-formal.sha256") files"
