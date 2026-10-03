#!/usr/bin/env bash
# Packager step (NEEDS NETWORK; not run by the judge): populate source/vendor
# (host workspace) and source/vendor-guest (guest workspace) from the pinned
# lockfiles, and record their content digests in dependency-locks/.
# Cargo additionally checks every vendored crate against the Cargo.lock
# checksums (.cargo-checksum.json) during the offline build.
set -euo pipefail
cd "$(dirname "$0")/../source"
rm -rf vendor vendor-guest
cargo vendor --locked vendor >/dev/null
( cd guest && cargo vendor --locked ../vendor-guest >/dev/null )
# Stub out Windows-only and wasm32-only (web-sys, js-sys) crates (never compiled on the x86_64-linux build
# image): keep Cargo.toml for resolution, drop sources, empty the per-file
# checksum list (cargo then checks only the package checksum from Cargo.lock).
# Cuts the expanded vendor tree from ~770 MB to ~300 MB.
for v in vendor vendor-guest; do
  for d in "$v"/windows* "$v"/winapi* "$v"/web-sys* "$v"/js-sys*; do
    [ -d "$d" ] || continue
    find "$d" -mindepth 1 -maxdepth 1 ! -name Cargo.toml ! -name .cargo-checksum.json -exec rm -rf {} +
    mkdir -p "$d/src" && echo '// stubbed by build-recipe/vendor.sh (windows-only crate)' > "$d/src/lib.rs"
    python3 - "$d/.cargo-checksum.json" <<'PY'
import json, sys
p = sys.argv[1]; j = json.load(open(p)); j["files"] = {}; json.dump(j, open(p, "w"))
PY
  done
done
for v in vendor vendor-guest; do
  d=$(cd "$v" && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
  echo "$d  source/$v ($(find "$v" -type f | wc -l) files)"
done > ../dependency-locks/vendor-digests.txt
cat ../dependency-locks/vendor-digests.txt
