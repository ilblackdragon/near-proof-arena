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
# challenge allowed_packages commit: near-transfer-receipt-v1-zk (challenges/drafts/,
# formal-core with ArenaCore.sha256Fast). formal-core/ and spec/lean/ are unchanged since.
PIN=e4088761c996284e25787bd61eabe8bf079bc914
pkg="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(git -C "$pkg" rev-parse --show-toplevel)"
NEARSPEC="Bytes SHA256 AccountId Primitives Trie Outcome TransferV1 ClaimCodec Challenge"   # runners/formal-checker/challenges/near-transfer-receipt-v1.json

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

# zk-formal: the working tree (lanes commit there first), sources only, and ONLY the
# modules in the import closure of formal/NpUdrStark/*.lean (the verifier model and
# the certificate): the judge elaborates every .lean file under formal/.
rm -rf "$pkg/formal/ZkFormal" "$pkg/formal/ZkFormal.lean"
python3 - "$repo/zk-formal" "$pkg/formal" <<'PY'
import os, re, shutil, sys
src, dst = sys.argv[1], sys.argv[2]
def imports(path):
    txt = open(path, encoding="utf-8").read()
    txt = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    txt = re.sub(r"--[^\n]*", "", txt)
    return re.findall(r"^\s*import\s+([A-Za-z0-9_.']+)", txt, flags=re.M)
todo = []
for f in sorted(os.listdir(os.path.join(dst, "NpUdrStark"))):
    if f.endswith(".lean"):
        todo += imports(os.path.join(dst, "NpUdrStark", f))
seen = set()
while todo:
    m = todo.pop()
    if m in seen or not m.startswith("ZkFormal"):
        continue
    seen.add(m)
    p = os.path.join(src, *m.split(".")) + ".lean"
    if not os.path.isfile(p):
        sys.exit(f"sync-lean: {m} not found in zk-formal")
    todo += imports(p)
for m in sorted(seen):
    rel = os.path.join(*m.split(".")) + ".lean"
    os.makedirs(os.path.dirname(os.path.join(dst, rel)), exist_ok=True)
    shutil.copyfile(os.path.join(src, rel), os.path.join(dst, rel))
print(f"zk-formal closure: {len(seen)} modules")
PY
( cd "$pkg/formal" && find ZkFormal -type f -name '*.lean' | LC_ALL=C sort | xargs sha256sum ) \
  > "$pkg/dependency-locks/zk-formal.sha256"
echo "lean-vendor: $(wc -l < "$pkg/dependency-locks/lean-vendor.sha256") files @ ${PIN:0:7}; zk-formal: $(wc -l < "$pkg/dependency-locks/zk-formal.sha256") files"
