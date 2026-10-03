#!/usr/bin/env bash
# Packager step (NEEDS NETWORK; not run by the judge): populate source/vendor
# (host workspace) and source/vendor-guest (guest workspace) from the pinned
# lockfiles, and record their content digests in dependency-locks/.
# Cargo additionally checks every vendored crate against the Cargo.lock
# checksums (.cargo-checksum.json) during the offline build.
set -euo pipefail
cd "$(dirname "$0")/../source"
rm -rf vendor vendor-guest
cargo vendor --locked --versioned-dirs vendor >/dev/null
( cd guest && cargo vendor --locked --versioned-dirs ../vendor-guest >/dev/null )
for v in vendor vendor-guest; do
  d=$(cd "$v" && find . -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
  echo "$d  source/$v ($(find "$v" -type f | wc -l) files)"
done > ../dependency-locks/vendor-digests.txt
cat ../dependency-locks/vendor-digests.txt
