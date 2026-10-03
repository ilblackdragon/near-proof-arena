#!/usr/bin/env bash
# Developer helper (NOT run by the build): refresh the vendored copies of the
# judge-trusted Lean packages (formal-core's ArenaCore, spec/lean's NearSpec)
# that the offline build compiles the Lean verifier against. Their tree digests
# are recorded in dependency-locks/lean-vendor.digests.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../../../.." && pwd)"
dst="$here/../lean-vendor"
rm -rf "$dst"
mkdir -p "$dst/formal-core" "$dst/spec/lean"
( cd "$repo/formal-core" && git ls-files ArenaCore.lean 'ArenaCore/*' lakefile.toml lean-toolchain lake-manifest.json | tar -cf - -T - ) | tar -xf - -C "$dst/formal-core"
( cd "$repo/spec/lean" && git ls-files NearSpec.lean 'NearSpec/*' lean-toolchain lake-manifest.json | tar -cf - -T - ) | tar -xf - -C "$dst/spec/lean"
# The vendored spec package only needs the trusted modules (no Codec/Examples/exe).
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
cat > "$dst/formal-core/lakefile.toml" <<'TOML'
name = "ArenaCore"
version = "0.1.0"

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

[[lean_lib]]
name = "ArenaCore"
TOML
rm -rf "$dst/spec/lean/NearSpec.lean" "$dst/spec/lean/NearSpec/Codec.lean" "$dst/spec/lean/NearSpec/Examples" "$dst/spec/lean/NearSpec/Examples.lean"
rm -f "$dst/spec/lean/lake-manifest.json" "$dst/formal-core/lake-manifest.json"
( cd "$dst" && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) > "$here/../../dependency-locks/lean-vendor.sha256"
echo "vendored into $dst"
