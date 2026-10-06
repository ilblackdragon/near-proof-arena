#!/usr/bin/env bash
# Developer helper (NOT run by the build): refresh the vendored copies of the
# judge-trusted Lean modules of challenge near-chunk-validation-d1
# (runners/formal-checker/challenges/near-chunk-validation-d1.json: formal-core's
# ArenaCore, spec/lean's NearSpec modules, spec/lean/v3's NearSpecV3 modules) that
# the offline build compiles the Lean verifier against. Exactly the trusted set
# the judge compiles and links, so out/verify is byte-identical to the judge
# build. Digests are recorded in dependency-locks/lean-vendor.sha256.
#   usage: sync-vendor.sh [COMMIT]   (default HEAD; must be the challenge's frozen tree)
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../../.." && pwd)"
rev="${1:-HEAD}"
dst="$here/../lean-vendor"
cfg="$repo/runners/formal-checker/challenges/near-chunk-validation-d1.json"
rm -rf "$dst"
mkdir -p "$dst"
mods=$(python3 - "$cfg" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
for t in c["trusted"]:
    for m in t["include"]:
        print(t["src_root"], m)
PY
)
tmp=$(mktemp -d)
git -C "$repo" archive "$rev" formal-core spec/lean | tar -x -C "$tmp"
while read -r root mod; do
  rel="${mod//.//}"
  if [ "$mod" = ArenaCore ]; then
    mkdir -p "$dst/$root"
    cp "$tmp/$root/ArenaCore.lean" "$dst/$root/"
    cp -R "$tmp/$root/ArenaCore" "$dst/$root/"
  else
    mkdir -p "$dst/$root/$(dirname "$rel")"
    cp "$tmp/$root/$rel.lean" "$dst/$root/$rel.lean"
  fi
done <<<"$mods"
rm -rf "$tmp"
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
cat > "$dst/spec/lean/v3/lakefile.toml" <<'TOML'
name = "NearSpecV3"
version = "0.1.0"

[[lean_lib]]
name = "NearSpecV3"
globs = ["NearSpecV3.+"]

[[require]]
name = "NearSpec"
path = ".."

[[require]]
name = "ArenaCore"
path = "../../../formal-core"
TOML
for d in formal-core spec/lean spec/lean/v3; do cp "$here/lean-toolchain" "$dst/$d/lean-toolchain"; done
( cd "$dst" && find . -type f ! -path '*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) > "$here/../../dependency-locks/lean-vendor.sha256"
echo "vendored $(wc -l < "$here/../../dependency-locks/lean-vendor.sha256") files from $rev into $dst"
