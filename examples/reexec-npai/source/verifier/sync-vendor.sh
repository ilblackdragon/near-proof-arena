#!/usr/bin/env bash
# Developer helper (NOT run by the build):
#  * refresh the vendored copies of the judge-trusted Lean packages
#    (formal-core's ArenaCore, spec/lean's trusted NearSpec modules) that the
#    offline build elaborates the program definition against;
#  * copy the NpaiIR library (examples/npai-ir) into formal/NpaiIR (the
#    candidate's Lean project must be self-contained);
#  * record the digests in dependency-locks/lean-vendor.sha256.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
pkg="$(cd "$here/../.." && pwd)"
repo="$(cd "$pkg/../.." && pwd)"
dst="$pkg/source/lean-vendor"
rm -rf "$dst"
mkdir -p "$dst/formal-core" "$dst/spec/lean"
( cd "$repo/formal-core" && git ls-files ArenaCore.lean 'ArenaCore/*' lean-toolchain | tar -cf - -T - ) | tar -xf - -C "$dst/formal-core"
( cd "$repo/spec/lean" && git ls-files 'NearSpec/*' lean-toolchain | tar -cf - -T - ) | tar -xf - -C "$dst/spec/lean"
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
rm -rf "$dst/spec/lean/NearSpec/Codec.lean" "$dst/spec/lean/NearSpec/Examples" "$dst/spec/lean/NearSpec/Examples.lean"
# NpaiIR library -> formal/NpaiIR
rm -rf "$pkg/formal/NpaiIR"
mkdir -p "$pkg/formal/NpaiIR/Lib"
( cd "$repo/examples/npai-ir" && git ls-files 'NpaiIR/*.lean' 'NpaiIR/Lib/*.lean' | grep -v '^NpaiIR/Example.lean$' | tar -cf - -T - ) | tar -xf - -C "$pkg/formal"
( cd "$dst" && find . -type f ! -path './*/.lake/*' | LC_ALL=C sort | xargs sha256sum ) > "$pkg/dependency-locks/lean-vendor.sha256"
echo "vendored into $dst and $pkg/formal/NpaiIR"
