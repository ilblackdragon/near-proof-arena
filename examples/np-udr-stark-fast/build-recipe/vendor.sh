#!/usr/bin/env bash
# Packager step (NEEDS NETWORK; not run by the judge): vendor every crate of
# the locked dependency graph (crates.io + the pinned Plonky3 git revision)
# into source/vendor/ and record its content digest. Cargo additionally
# verifies each vendored crate against the Cargo.lock checksums during the
# offline judge build.
set -euo pipefail
cd "$(dirname "$0")/../source"
rm -rf vendor
cargo vendor --locked --versioned-dirs vendor > /dev/null
# Windows-only crates are never compiled on the x86_64-linux build image:
# keep Cargo.toml for resolution, drop their sources and per-file checksums.
for d in vendor/windows* vendor/winapi*; do
  [ -d "$d" ] || continue
  find "$d" -mindepth 1 -maxdepth 1 ! -name Cargo.toml ! -name .cargo-checksum.json -exec rm -rf {} +
  mkdir -p "$d/src" && echo '// stubbed by build-recipe/vendor.sh (windows-only crate)' > "$d/src/lib.rs"
  python3 - "$d/.cargo-checksum.json" <<'PY'
import json, sys
p = sys.argv[1]; j = json.load(open(p)); j["files"] = {}; json.dump(j, open(p, "w"))
PY
done
d=$(find vendor -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
echo "$d  source/vendor ($(find vendor -type f | wc -l) files)" > ../dependency-locks/vendor-digest.txt
cp Cargo.lock ../dependency-locks/Cargo.lock
cat ../dependency-locks/vendor-digest.txt
