#!/usr/bin/env bash
# Build the pinned build-toolchain image used as the candidate root for
# `build` jobs (worker BuildJob.toolchain_image / Rootfs::Image).
#
# The pinned Docker image (rust 1.96.0 + gcc 12 on Debian bookworm) is
# flattened into a plain directory that satisfies the CONTRACTS §1 tree rules
# (no symlinks, hardlinks, devices, setuid): symlinks are dereferenced,
# hardlinks split, dangling links dropped, setuid/setgid/sticky bits cleared.
# The directory is named by its TreeDigest:
#   $TOOLCHAIN_IMAGES/<hex>/         (default /data/illia/nearproof-deps/toolchain-images)
#   $TOOLCHAIN_IMAGES/<hex>.json     identity + the env a build must use
# The digest depends only on file contents/modes, so rebuilding from the same
# pinned base reproduces it (`--check` builds twice and compares).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
# shellcheck source=../firecracker/PINS
source "$here/../firecracker/PINS"
OUT=${TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}
mkdir -p "$OUT"

(cd "$repo" && cargo build -q --release -p arena-firecracker --bin arena-tree-digest)
digest_bin="$repo/target/release/arena-tree-digest"

docker image inspect "$TOOLCHAIN_BASE_IMAGE" >/dev/null 2>&1 || docker pull -q "$TOOLCHAIN_BASE_IMAGE" >/dev/null

flatten() { # dest
  local dest=$1
  mkdir -p "$dest"
  docker run --rm --network none --cap-drop ALL --cap-add DAC_READ_SEARCH --cap-add FOWNER \
    "$TOOLCHAIN_BASE_IMAGE" sh -euc '
      # dangling symlinks cannot be dereferenced; drop them
      find / -xdev -xtype l -delete 2>/dev/null || true
      rm -rf /usr/share/doc /usr/share/man /usr/share/info /usr/share/locale \
             /usr/local/rustup/toolchains/*/share/doc /usr/local/rustup/downloads /usr/local/rustup/tmp
      tar -C / --dereference --hard-dereference --numeric-owner -cf - \
          bin sbin lib lib64 usr etc
    ' | tar -C "$dest" -xpf - --no-same-owner
  # files Docker bind-mounts per container
  : > "$dest/etc/hostname"; : > "$dest/etc/resolv.conf"
  printf '127.0.0.1 localhost\n' > "$dest/etc/hosts"
  # contract tree rules: paths must be unique under case folding (the
  # kernel's netfilter headers ship e.g. xt_CONNMARK.h and xt_connmark.h);
  # drop the non-lowercase member of each colliding pair.
  python3 - "$dest" <<'PY'
import os, sys
root = sys.argv[1]
removed = []
for d, dirs, files in os.walk(root):
    names = dirs + files
    groups = {}
    for n in names:
        groups.setdefault(n.casefold(), []).append(n)
    for g in groups.values():
        if len(g) > 1:
            keep = min(g, key=lambda n: (n != n.lower(), n))
            for n in g:
                if n != keep:
                    p = os.path.join(d, n)
                    if os.path.isdir(p) and not os.path.islink(p):
                        raise SystemExit(f"case collision on directory {p}")
                    os.remove(p)
                    removed.append(os.path.relpath(p, root))
print("\n".join(sorted(removed)), file=open(root + ".case-removed", "w"))
PY
  # contract tree rules: no setuid/setgid/sticky bits on files
  find "$dest" -type f -perm /7000 -exec chmod ug-s,o-t {} +
  chmod -R u+rwX "$dest"
}

tmp=$(mktemp -d "$OUT/.build.XXXXXX")
[[ -n ${KEEP_WORK:-} ]] || trap 'chmod -R u+w "$tmp" 2>/dev/null; rm -rf "$tmp"' EXIT
flatten "$tmp/a"
read -r digest files bytes < <("$digest_bin" "$tmp/a")
if [[ ${1:-} == --check ]]; then
  flatten "$tmp/b"
  read -r digest_b _ _ < <("$digest_bin" "$tmp/b")
  [[ $digest == "$digest_b" ]] || { echo "NOT reproducible: $digest != $digest_b" >&2; exit 1; }
  echo "reproducible: two flattenings -> $digest" >&2
fi
hex=${digest#sha256:}
if [[ -d "$OUT/$hex" ]]; then
  echo "already installed: $OUT/$hex" >&2
else
  mv "$tmp/a" "$OUT/$hex"
fi
rustc_v=$(docker run --rm --network none "$TOOLCHAIN_BASE_IMAGE" rustc -V)
cc_v=$(docker run --rm --network none "$TOOLCHAIN_BASE_IMAGE" sh -c 'cc --version | head -1')
tc_bin="/usr/local/rustup/toolchains/$TOOLCHAIN_RUST/bin"
cat > "$OUT/$hex.json" <<EOM
{
  "digest": "$digest",
  "files": $files,
  "bytes": $bytes,
  "base_image": "$TOOLCHAIN_BASE_IMAGE",
  "rustc": "$rustc_v",
  "cc": "$cc_v",
  "lean": null,
  "case_collisions_removed": $(python3 -c 'import json,sys; print(json.dumps([l for l in open(sys.argv[1]).read().split("\n") if l]))' "$tmp/a.case-removed"),
  "env": {
    "PATH": "$tc_bin:/usr/local/bin:/usr/bin:/bin",
    "CARGO_HOME": "/scratch/.cargo",
    "CARGO_NET_OFFLINE": "true"
  },
  "offline_deps": "vendor crates into the package (cargo vendor) and point .cargo/config.toml [source] replacement at the vendored dir; no registry or network exists in the build VM"
}
EOM
echo "$digest"
