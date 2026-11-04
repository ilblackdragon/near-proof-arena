#!/usr/bin/env bash
# D-8: regenerate patches/e2e-tree.patch = diff(d4h + e2e-heights.patch, pq-e2e-d7) over the files the
# D-6 patch touched plus nv/hash.rs, then check d4h + e2e-heights + e2e-tree reproduces d8 byte for byte.
set -euo pipefail
. "$(cd "$(dirname "$0")" && pwd)/env_d8.sh"
R=$W/research/near-compression/native/recursion/patches
H=$R/e2e-heights.patch; P=$R/e2e-tree.patch
T=$(mktemp -d /data/illia/nearproof-deps/.treechk.XXXX); trap 'rm -rf "$T"' EXIT
FILES=$( (grep -h '^+++ b/' "$H" "$P"; echo "+++ b/openvm-sha384/crates/recursion/src/nv/hash.rs") | sed 's|^+++ b/||' | sort -u)
mkdir -p "$T/base"
for f in $FILES; do
  mkdir -p "$T/base/$(dirname "$f")"
  if [ -f "/data/illia/nearproof-deps/pq-e2e-d4h/$f" ]; then cp "/data/illia/nearproof-deps/pq-e2e-d4h/$f" "$T/base/$f"; fi
done
(cd "$T/base" && patch -s -p1 < "$H")
NEW=$T/new.patch; : > "$NEW"
for f in $(grep -h '^+++ b/' "$P" | sed 's|^+++ b/||'; echo openvm-sha384/crates/recursion/src/nv/hash.rs); do
  [ -n "$(grep -x "$f" <<< "$FILES")" ] || continue
  if [ -f "$T/base/$f" ]; then a="$T/base/$f"; else a=/dev/null; fi
  diff -u --label "a/$f" --label "b/$f" "$a" "$D/$f" >> "$NEW" || true
done
# keep file order unique (hash.rs may already be listed)
python3 - "$NEW" <<'PY'
import sys, re
s = open(sys.argv[1]).read()
parts = re.split(r'(?m)^(?=--- a/)', s)
seen, out = set(), []
for p in parts:
    if not p.strip():
        continue
    m = re.match(r'--- a/(\S+)', p)
    if m.group(1) in seen:
        continue
    seen.add(m.group(1)); out.append(p)
open(sys.argv[1], 'w').write(''.join(out))
PY
cp "$NEW" "$P"
# check
mkdir -p "$T/chk"
for f in $FILES; do
  mkdir -p "$T/chk/$(dirname "$f")"
  if [ -f "/data/illia/nearproof-deps/pq-e2e-d4h/$f" ]; then cp "/data/illia/nearproof-deps/pq-e2e-d4h/$f" "$T/chk/$f"; fi
done
(cd "$T/chk" && patch -s -p1 < "$H" && patch -s -p1 < "$P")
n=0
for f in $FILES; do cmp -s "$T/chk/$f" "$D/$f" || { echo "DIFF d8 $f"; n=1; }; done
sha256sum "$H" "$P"; wc -l "$P"
[ $n = 0 ] && echo "E2E_HEIGHTS_AND_TREE_PATCHES_REPRODUCE_D8"
