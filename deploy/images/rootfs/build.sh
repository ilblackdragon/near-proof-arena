#!/usr/bin/env bash
# Build the arena guest rootfs (ext4, read-only at runtime) reproducibly.
#
# Inputs (all pinned): BASE_IMAGE from ../firecracker/PINS, the static
# arena-init built from this checkout (../build-static.sh), e2fsprogs from the
# same pinned base image. Output:
#   $ARENA_FC_DEPS/images/rootfs-<sha12>.ext4   (mode 0444)
#   $ARENA_FC_DEPS/images/rootfs.ext4 -> symlink to the above
#   $ARENA_FC_DEPS/images/rootfs.ext4.sha256
# Determinism: the tree is extracted into a tmpfs, mtimes clamped to
# SOURCE_DATE_EPOCH, fixed fs UUID / hash seed, E2FSPROGS_FAKE_TIME.
# `--check` builds twice and fails unless both images are bit-identical.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=../firecracker/PINS
source "$here/../firecracker/PINS"
DEPS=${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}
SOURCE_DATE_EPOCH=${SOURCE_DATE_EPOCH:-1767225600}   # 2026-01-01T00:00:00Z
FS_UUID=6172656e-612d-726f-6f74-66732d763100            # "arena-rootfs-v1"
SIZE_MB=${ROOTFS_SIZE_MB:-160}

bin=$("$here/../build-static.sh")
work=$(mktemp -d "${TMPDIR:-/tmp}/arena-rootfs.XXXXXX")
[[ -n ${KEEP_WORK:-} ]] || trap 'rm -rf "$work"' EXIT
cp "$bin/arena-init" "$work/arena-init"

docker image inspect "$BASE_IMAGE" >/dev/null 2>&1 || docker pull -q "$BASE_IMAGE" >/dev/null
cid=$(docker create --network none "$BASE_IMAGE" /bin/true)
docker export "$cid" > "$work/base.tar"
docker rm "$cid" >/dev/null

build_once() { # outname
  docker run --rm --network none --cap-drop ALL --cap-add CHOWN --cap-add FOWNER \
    --cap-add DAC_OVERRIDE --cap-add MKNOD --cap-add SETFCAP \
    --tmpfs /build:size=1g,exec,dev \
    -e SOURCE_DATE_EPOCH="$SOURCE_DATE_EPOCH" -e E2FSPROGS_FAKE_TIME="$SOURCE_DATE_EPOCH" \
    -v "$work:/w" "$BASE_IMAGE" bash -euo pipefail -c '
      r=/build/root; mkdir $r
      tar -xpf /w/base.tar -C $r --numeric-owner
      # docker-generated runtime files and caches
      rm -f $r/.dockerenv
      : > $r/etc/hostname; : > $r/etc/resolv.conf
      printf "127.0.0.1 localhost\n" > $r/etc/hosts
      rm -rf $r/var/cache/* $r/var/lib/apt/lists/* $r/var/log/* $r/usr/share/doc/* $r/usr/share/man/*
      # candidate identity
      echo "arena:x:1000:1000:arena candidate:/arena/scratch:/usr/sbin/nologin" >> $r/etc/passwd
      echo "arena:x:1000:" >> $r/etc/group
      echo "arena:!:20454::::::" >> $r/etc/shadow
      # no setuid/setgid escalation paths inside the guest
      find $r -xdev -type f -perm /6000 -exec chmod ug-s {} +
      install -m 0755 /w/arena-init $r/sbin/arena-init
      mkdir -m 0755 $r/arena
      find $r -xdev -exec touch -h -d @$SOURCE_DATE_EPOCH {} +
      mkfs.ext4 -q -F -L arena-rootfs -U '"$FS_UUID"' \
        -E hash_seed='"$FS_UUID"',root_owner=0:0,lazy_itable_init=0,nodiscard \
        -O ^has_journal,^metadata_csum_seed -m 0 -b 4096 -I 256 \
        -d $r /build/out.ext4 '"$SIZE_MB"'M
      # mke2fs -d copies each source inode ctime (= extraction time, which
      # cannot be set from userspace); clamp it with debugfs.
      ts=$(date -u -d @$SOURCE_DATE_EPOCH +%Y%m%d%H%M%S)
      if find $r -name "*\"*" | grep -q .; then echo "quote in path" >&2; exit 1; fi
      { echo "set_inode_field / ctime $ts"
        (cd $r && find . -mindepth 1 -printf "%P\n") | sort | while IFS= read -r p; do
          printf "set_inode_field \"/%s\" ctime %s\n" "$p" "$ts"; done
      } > /build/ctime.cmd
      debugfs -w -f /build/ctime.cmd /build/out.ext4 >/dev/null 2>/build/debugfs.err
      if grep -v "^debugfs " /build/debugfs.err | grep -q .; then cat /build/debugfs.err >&2; exit 1; fi
      e2fsck -fn /build/out.ext4 >/dev/null
      cp /build/out.ext4 /w/'"$1"'
    '
}

build_once a.ext4
sum=$(sha256sum "$work/a.ext4" | cut -d" " -f1)
if [[ ${1:-} == --check ]]; then
  build_once b.ext4
  sum_b=$(sha256sum "$work/b.ext4" | cut -d" " -f1)
  if [[ $sum != "$sum_b" ]]; then
    echo "NOT reproducible: $sum != $sum_b" >&2
    exit 1
  fi
  echo "reproducible: two builds -> $sum" >&2
fi

mkdir -p "$DEPS/images"
out="$DEPS/images/rootfs-${sum:0:12}.ext4"
install -m 0444 "$work/a.ext4" "$out"
ln -sfn "$(basename "$out")" "$DEPS/images/rootfs.ext4"
echo "sha256:$sum" > "$DEPS/images/rootfs.ext4.sha256"
init_sum=$(sha256sum "$bin/arena-init" | cut -d" " -f1)
cat > "$DEPS/images/rootfs.manifest" <<EOM
rootfs=$(basename "$out")
rootfs_sha256=$sum
base_image=$BASE_IMAGE
arena_init_sha256=$init_sum
source_date_epoch=$SOURCE_DATE_EPOCH
size_mb=$SIZE_MB
EOM
echo "$out sha256:$sum"
