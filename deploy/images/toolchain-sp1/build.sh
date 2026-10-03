#!/usr/bin/env bash
# Build the SP1 build-toolchain image: the pinned base build-toolchain image
# (deploy/images/toolchain/build.sh, rust 1.96.0 + gcc 12, identified by its
# TreeDigest) plus SP1's `succinct` Rust toolchain for the
# riscv64im-succinct-zkvm-elf target, installed as the rustup custom toolchain
# /usr/local/rustup/toolchains/succinct. With it, a candidate's build recipe
# can rebuild an SP1 guest from source (`rustup run succinct rustc ...`)
# instead of shipping a pre-built guest ELF.
#
# Inputs are pinned by digest:
#   * the base image directory: its TreeDigest (SP1_BASE_IMAGE) is recomputed
#     and must match before anything is copied;
#   * the succinct toolchain release tarball (SUCCINCT_* below): the same
#     asset `cargo prove install-toolchain` (SP1 v6.8.1) downloads; its sha256
#     is checked (it also equals the digest GitHub publishes for the asset).
# The output directory is named by its TreeDigest and depends only on file
# contents/modes, so rebuilding from the same inputs reproduces it
# (`--check` builds twice and compares).
#
#   $TOOLCHAIN_IMAGES/<hex>/      (default /data/illia/nearproof-deps/toolchain-images)
#   $TOOLCHAIN_IMAGES/<hex>.json  identity + the env a build must use
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
OUT=${TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}
SP1_BASE_IMAGE=${SP1_BASE_IMAGE:-sha256:57a89fc650b89d189677fad047e7af1881860c7083b51ea07f0d729a28ebc117}
SUCCINCT_TAG=succinct-1.96.0-64bit-v2
SUCCINCT_URL=https://github.com/succinctlabs/rust/releases/download/$SUCCINCT_TAG/rust-toolchain-x86_64-unknown-linux-gnu.tar.gz
SUCCINCT_SHA256=ff3afc3a6f22af93d162652972f254fcecf443ca4b2de18897312f19997fb94b
# Where a previously downloaded copy may be found (checked by sha256 like a download).
SUCCINCT_TARBALL=${SUCCINCT_TARBALL:-$HOME/.sp1/rust-toolchain-x86_64-unknown-linux-gnu.tar.gz}

(cd "$repo" && cargo build -q --release -p arena-firecracker --bin arena-tree-digest)
digest_bin="$repo/target/release/arena-tree-digest"

base="$OUT/${SP1_BASE_IMAGE#sha256:}"
[[ -d $base ]] || { echo "base image $SP1_BASE_IMAGE not installed under $OUT (deploy/images/toolchain/build.sh)" >&2; exit 1; }
read -r got _ _ < <("$digest_bin" "$base")
[[ $got == "$SP1_BASE_IMAGE" ]] || { echo "base image dir digest $got != $SP1_BASE_IMAGE" >&2; exit 1; }

tmp=$(mktemp -d "$OUT/.build-sp1.XXXXXX")
[[ -n ${KEEP_WORK:-} ]] || trap 'chmod -R u+w "$tmp" 2>/dev/null; rm -rf "$tmp"' EXIT

tarball="$tmp/succinct.tar.gz"
if [[ -f $SUCCINCT_TARBALL ]]; then
  cp "$SUCCINCT_TARBALL" "$tarball"
else
  curl -fsSL -o "$tarball" "$SUCCINCT_URL"
fi
echo "$SUCCINCT_SHA256  $tarball" | sha256sum -c --quiet - \
  || { echo "succinct toolchain tarball sha256 mismatch (want $SUCCINCT_SHA256)" >&2; exit 1; }

assemble() { # dest
  local dest=$1 tc
  cp -a "$base" "$dest"
  tc="$dest/usr/local/rustup/toolchains/succinct"
  [[ ! -e $tc ]] || { echo "base image already has a succinct toolchain" >&2; exit 1; }
  mkdir -p "$tc"
  tar -C "$tc" -xzf "$tarball" --no-same-owner --no-same-permissions
  # contract tree rules: no symlinks, hardlinks (split), setuid/setgid/sticky bits
  find "$tc" -type l -print -quit | grep -q . && { echo "symlink in toolchain tarball" >&2; exit 1; }
  find "$tc" -type f -links +1 -print0 | while IFS= read -r -d '' f; do
    cp -p "$f" "$f.split" && mv -f "$f.split" "$f"
  done
  find "$tc" -type f -perm /7000 -exec chmod ug-s,o-t {} +
  # modes as the base flattening normalizes them (u+rwX; exec bit kept)
  chmod -R u+rwX,go+rX,go-w "$tc"
}

assemble "$tmp/a"
read -r digest files bytes < <("$digest_bin" "$tmp/a")
if [[ ${1:-} == --check ]]; then
  assemble "$tmp/b"
  read -r digest_b _ _ < <("$digest_bin" "$tmp/b")
  [[ $digest == "$digest_b" ]] || { echo "NOT reproducible: $digest != $digest_b" >&2; exit 1; }
  echo "reproducible: two assemblies -> $digest" >&2
fi
hex=${digest#sha256:}
if [[ -d "$OUT/$hex" ]]; then
  echo "already installed: $OUT/$hex" >&2
else
  mv "$tmp/a" "$OUT/$hex"
fi
base_json="$OUT/${SP1_BASE_IMAGE#sha256:}.json"
python3 - "$base_json" "$OUT/$hex.json" "$digest" "$files" "$bytes" "$SP1_BASE_IMAGE" \
  "$SUCCINCT_TAG" "$SUCCINCT_URL" "$SUCCINCT_SHA256" <<'PY'
import json, sys
src, dst, digest, files, nbytes, base, tag, url, sha = sys.argv[1:]
b = json.load(open(src))
b.update({
    "digest": digest, "files": int(files), "bytes": int(nbytes),
    "derived_from": base,
    "succinct_toolchain": {"tag": tag, "url": url, "sha256": sha,
                           "rustc": "rustc 1.96.0-dev", "target": "riscv64im-succinct-zkvm-elf",
                           "path": "/usr/local/rustup/toolchains/succinct"},
})
b["env"] = dict(b.get("env", {}))
b["env"]["RUSTUP_HOME"] = "/usr/local/rustup"
b["env"]["PATH"] = "/usr/local/rustup/toolchains/1.96.0-x86_64-unknown-linux-gnu/bin:/usr/local/cargo/bin:/usr/local/bin:/usr/bin:/bin"
json.dump(b, open(dst, "w"), indent=2)
open(dst, "a").write("\n")
PY
echo "$digest"
