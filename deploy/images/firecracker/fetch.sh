#!/usr/bin/env bash
# Download and verify the pinned Firecracker/jailer release and guest kernel.
# Idempotent; refuses to install anything whose sha256 does not match PINS.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=PINS
source "$here/PINS"
DEPS=${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}
mkdir -p "$DEPS/dl" "$DEPS/bin" "$DEPS/kernel"

fetch() { # url sha256 dest
  local url=$1 sum=$2 dest=$3
  if [[ -f $dest ]] && echo "$sum  $dest" | sha256sum -c --status; then return 0; fi
  curl -fsSL --retry 3 -o "$dest.part" "$url"
  echo "$sum  $dest.part" | sha256sum -c --status || { echo "sha256 mismatch for $url" >&2; rm -f "$dest.part"; exit 1; }
  mv "$dest.part" "$dest"
}

fetch "$FC_TGZ_URL" "$FC_TGZ_SHA256" "$DEPS/dl/firecracker-$FC_VERSION-x86_64.tgz"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
tar -xzf "$DEPS/dl/firecracker-$FC_VERSION-x86_64.tgz" -C "$tmp"
rel="$tmp/release-$FC_VERSION-x86_64"
echo "$FIRECRACKER_SHA256  $rel/firecracker-$FC_VERSION-x86_64" | sha256sum -c --status
echo "$JAILER_SHA256  $rel/jailer-$FC_VERSION-x86_64" | sha256sum -c --status
install -m 0555 "$rel/firecracker-$FC_VERSION-x86_64" "$DEPS/bin/firecracker"
install -m 0555 "$rel/jailer-$FC_VERSION-x86_64" "$DEPS/bin/jailer"

fetch "$KERNEL_URL" "$KERNEL_SHA256" "$DEPS/kernel/vmlinux-$KERNEL_VERSION"
fetch "$KERNEL_CONFIG_URL" "$KERNEL_CONFIG_SHA256" "$DEPS/kernel/vmlinux-$KERNEL_VERSION.config"
chmod 0444 "$DEPS/kernel/vmlinux-$KERNEL_VERSION"
# the guest kernel must not support loadable modules
if grep -q '^CONFIG_MODULES=y' "$DEPS/kernel/vmlinux-$KERNEL_VERSION.config"; then
  echo "pinned kernel has CONFIG_MODULES=y" >&2; exit 1
fi

ln -sfn "vmlinux-$KERNEL_VERSION" "$DEPS/kernel/vmlinux"
echo "sha256:$KERNEL_SHA256" > "$DEPS/kernel/vmlinux.sha256"

fetch "$DOCKER_SECCOMP_URL" "$DOCKER_SECCOMP_SHA256" "$DEPS/dl/docker-default-seccomp.json"

echo "firecracker $FC_VERSION, jailer, kernel $KERNEL_VERSION verified in $DEPS"
