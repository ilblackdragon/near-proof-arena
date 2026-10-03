#!/usr/bin/env bash
# Build the pinned Lean checker image: a candidate-root directory image (same
# rules as deploy/images/toolchain) for formal checking and for judge-built
# native-lean verifiers, run inside Firecracker microVMs.
#
# Layout of the image (guest paths match runners/formal-checker's pipeline):
#   /arena/tc/                 Lean toolchain (elan-free; bin/{lean,lake,leanc,
#                              leanchecker,clang,ld.lld,...}, lib/, include/;
#                              leanc uses the bundled clang + lld + glibc stubs)
#   /arena/tools/lean4export   pinned in runners/formal-checker/tools.toml
#   /arena/tools/nanoda_bin    "
#   /arena/tools/lean4lean     "
#   /arena/tools/arena-audit   runners/formal-checker/lean/ArenaAudit (this repo)
#   /bin /lib /usr /etc ...    flattened pinned debian:bookworm-slim (glibc, sh)
#
# Output: $LEAN_CHECKER_IMAGES/<hex>/ and <hex>.json (identity, tool digests,
# env). `--check` builds everything twice (tools from source too) and fails
# unless the two images have the same TreeDigest.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=../firecracker/PINS
source "$here/../firecracker/PINS"
FCDIR="$repo/runners/formal-checker"
TOOLCHAIN=$(tr -d '[:space:]' < "$FCDIR/lean-toolchain")
[[ $TOOLCHAIN == "leanprover/lean4:$LEAN_VERSION" ]] || {
  echo "formal-checker lean-toolchain ($TOOLCHAIN) != PINS LEAN_VERSION ($LEAN_VERSION)" >&2; exit 1; }
WORK=${LEAN_CHECKER_WORK:-/data/illia/nearproof-deps/lean-checker}
OUT=${LEAN_CHECKER_IMAGES:-$WORK/images}
mkdir -p "$WORK/dl" "$WORK/src" "$OUT"
uidgid="$(id -u):$(id -g)"

toml_get() { # section key
  awk -v s="[$1]" -v k="$2" '$0==s{f=1;next} /^\[/{f=0} f && $1==k {gsub(/"/,"",$3); print $3}' "$FCDIR/tools.toml"
}

# --- pinned inputs ----------------------------------------------------------
tarball="$WORK/dl/lean-${LEAN_VERSION#v}-linux.tar.zst"
if ! echo "$LEAN_TARBALL_SHA256  $tarball" | sha256sum -c --status 2>/dev/null; then
  curl -fsSL --retry 3 -o "$tarball.part" "$LEAN_TARBALL_URL"
  echo "$LEAN_TARBALL_SHA256  $tarball.part" | sha256sum -c --status || { echo "lean tarball sha256 mismatch" >&2; exit 1; }
  mv "$tarball.part" "$tarball"
fi
clone() { # name repo rev -> prints dir
  local d="$WORK/src/$1-$3"
  if [[ ! -d $d/.git ]]; then
    git clone -q "$2" "$d.tmp" && mv "$d.tmp" "$d"
  fi
  git -C "$d" checkout -q --detach "$3"
  [[ $(git -C "$d" rev-parse HEAD) == "$3" ]] || { echo "$1: rev mismatch" >&2; exit 1; }
  echo "$d"
}
EXPORT_REV=$(toml_get lean4export rev); NANODA_REV=$(toml_get nanoda rev)
L4L_REV=$(toml_get lean4lean rev); BATT_REV=$(toml_get lean4lean batteries_rev)
SRC_EXPORT=$(clone lean4export "$(toml_get lean4export repo)" "$EXPORT_REV")
SRC_NANODA=$(clone nanoda_lib "$(toml_get nanoda repo)" "$NANODA_REV")
SRC_L4L=$(clone lean4lean "$(toml_get lean4lean repo)" "$L4L_REV")
for img in "$LEAN_BUILDER_IMAGE" "$TOOLCHAIN_BASE_IMAGE" "$BASE_IMAGE"; do
  docker image inspect "$img" >/dev/null 2>&1 || docker pull -q "$img" >/dev/null
done
(cd "$repo" && cargo build -q --release -p arena-firecracker --bin arena-tree-digest)
digest_bin="$repo/target/release/arena-tree-digest"

# --- one full build into $1 --------------------------------------------------
build_image() { # dest_root
  local root=$1 b; b=$(mktemp -d "$WORK/.b.XXXXXX")
  mkdir -p "$b/tc" "$b/src" "$b/build" "$b/out" "$root"
  tar --zstd -xf "$tarball" -C "$b/tc" --strip-components=1
  # sources (no .git), ArenaAudit from this checkout
  for s in "$SRC_EXPORT:lean4export" "$SRC_NANODA:nanoda" "$SRC_L4L:lean4lean"; do
    mkdir -p "$b/src/${s##*:}"; git -C "${s%%:*}" archive HEAD | tar -x -C "$b/src/${s##*:}"
  done
  mkdir -p "$b/src/ArenaAudit"
  (cd "$FCDIR/lean/ArenaAudit" && tar --exclude=.lake -chf - .) | tar -x -C "$b/src/ArenaAudit"

  # Lean tools: lake + bundled clang, fixed paths, builder with git for lake
  docker run --rm --user "$uidgid" -e HOME=/build/home \
    -v "$b/tc:/opt/lean:ro" -v "$b/src:/src:ro" -v "$b/build:/build" -v "$b/out:/out" \
    "$LEAN_BUILDER_IMAGE" bash -euo pipefail -c '
      export PATH=/opt/lean/bin:$PATH; mkdir -p $HOME
      cp -r /src/lean4export /build/lean4export && cd /build/lean4export
      echo "'"$TOOLCHAIN"'" > lean-toolchain
      lake build -q lean4export && install -m 0755 .lake/build/bin/lean4export /out/
      cp -r /src/lean4lean /build/lean4lean && cd /build/lean4lean
      echo "'"$TOOLCHAIN"'" > lean-toolchain
      sed -i -E "/name = \"batteries\"/,/rev =/ s/^rev = .*/rev = \"'"$BATT_REV"'\"/" lakefile.toml
      rm -f lake-manifest.json
      lake build -q lean4lean && install -m 0755 .lake/build/bin/lean4lean /out/
      cp -r /src/ArenaAudit /build/ArenaAudit && cd /build/ArenaAudit
      echo "'"$TOOLCHAIN"'" > lean-toolchain
      lake build -q arena-audit && install -m 0755 .lake/build/bin/arena-audit /out/
    ' >&2
  # nanoda (Rust): locked deps, fixed paths, stripped
  docker run --rm --user "$uidgid" -e CARGO_HOME=/build/cargo -e HOME=/build \
    -e RUSTFLAGS="-C strip=symbols --remap-path-prefix=/build=/b" \
    -v "$b/src:/src:ro" -v "$b/build:/build" -v "$b/out:/out" \
    "$TOOLCHAIN_BASE_IMAGE" bash -euo pipefail -c '
      cp -r /src/nanoda /build/nanoda && cd /build/nanoda
      cargo build -q --release --locked --bin nanoda_bin && install -m 0755 target/release/nanoda_bin /out/
    ' >&2

  # root: flattened debian base + toolchain + tools
  docker run --rm --network none "$BASE_IMAGE" sh -euc '
      find / -xdev -xtype l -delete 2>/dev/null || true
      rm -rf /usr/share/doc /usr/share/man /usr/share/info /usr/share/locale /var/cache/* /var/lib/apt/lists/*
      tar -C / --dereference --hard-dereference --numeric-owner -cf - bin sbin lib lib64 usr etc
    ' | tar -C "$root" -xpf - --no-same-owner
  : > "$root/etc/hostname"; : > "$root/etc/resolv.conf"
  printf '127.0.0.1 localhost\n' > "$root/etc/hosts"
  mkdir -p "$root/arena/tc" "$root/arena/tools"
  cp -rL --preserve=mode "$b/tc/." "$root/arena/tc/"
  install -m 0755 "$b/out/"{lean4export,nanoda_bin,lean4lean,arena-audit} "$root/arena/tools/"
  python3 "$here/../lib/sanitize_tree.py" "$root"
  chmod -R u+w "$b"; rm -rf "$b"
}

tmp=$(mktemp -d "$OUT/.build.XXXXXX")
[[ -n ${KEEP_WORK:-} ]] || trap 'chmod -R u+w "$tmp" 2>/dev/null; rm -rf "$tmp"' EXIT
t0=$(date +%s)
build_image "$tmp/a"
t1=$(date +%s)
read -r digest files bytes < <("$digest_bin" "$tmp/a")
if [[ ${1:-} == --check ]]; then
  build_image "$tmp/b"
  read -r digest_b _ _ < <("$digest_bin" "$tmp/b")
  if [[ $digest != "$digest_b" ]]; then
    diff -rq "$tmp/a" "$tmp/b" | head -20 >&2
    echo "NOT reproducible: $digest != $digest_b" >&2; exit 1
  fi
  echo "reproducible: two independent builds -> $digest" >&2
fi
hex=${digest#sha256:}
if [[ -d "$OUT/$hex" ]]; then echo "already installed: $OUT/$hex" >&2; else mv "$tmp/a" "$OUT/$hex"; fi
sum() { sha256sum "$OUT/$hex/$1" | cut -d' ' -f1; }
cat > "$OUT/$hex.json" <<EOM
{
  "digest": "$digest",
  "files": $files,
  "bytes": $bytes,
  "build_seconds": $((t1 - t0)),
  "lean_toolchain": "$TOOLCHAIN",
  "lean_tarball_sha256": "$LEAN_TARBALL_SHA256",
  "base_image": "$BASE_IMAGE",
  "builder_images": ["$LEAN_BUILDER_IMAGE", "$TOOLCHAIN_BASE_IMAGE"],
  "tools": {
    "lean4export": {"rev": "$EXPORT_REV", "sha256": "$(sum arena/tools/lean4export)"},
    "nanoda_bin": {"rev": "$NANODA_REV", "sha256": "$(sum arena/tools/nanoda_bin)"},
    "lean4lean": {"rev": "$L4L_REV", "batteries_rev": "$BATT_REV", "sha256": "$(sum arena/tools/lean4lean)"},
    "arena-audit": {"repo_commit": "$(git -C "$repo" rev-parse HEAD)", "sha256": "$(sum arena/tools/arena-audit)"}
  },
  "case_collisions_removed": $(python3 -c 'import json,sys; print(json.dumps([l for l in open(sys.argv[1]).read().split("\n") if l]))' "$tmp/a.case-removed" 2>/dev/null || echo '[]'),
  "env": {
    "PATH": "/arena/tc/bin:/usr/bin:/bin",
    "ARENA_LEAN_SYSROOT": "/arena/tc"
  }
}
EOM
echo "$digest"
