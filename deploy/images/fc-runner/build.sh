#!/usr/bin/env bash
# Build the delivery image `arena-fc-runner:<tag>` from the pinned
# firecracker/jailer (verified by ../firecracker/fetch.sh) and the static
# shim from this checkout, and (re)generate the container seccomp profile.
# Prints the image id (sha256:...), which the runner config should pin.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=../firecracker/PINS
source "$here/../firecracker/PINS"
DEPS=${ARENA_FC_DEPS:-/data/illia/nearproof-deps/firecracker}
"$here/../firecracker/fetch.sh" >&2
bin=$("$here/../build-static.sh")
ctx=$(mktemp -d "${TMPDIR:-/tmp}/arena-fc-runner.XXXXXX")
trap 'rm -rf "$ctx"' EXIT
install -m 0555 "$DEPS/bin/firecracker" "$DEPS/bin/jailer" "$bin/arena-fc-shim" "$ctx/"
cp "$here/Dockerfile" "$ctx/"
shim_sum=$(sha256sum "$bin/arena-fc-shim" | cut -c1-12)
tag="arena-fc-runner:fc-${FC_VERSION#v}-shim-$shim_sum"
docker build -q --network none -t "$tag" -t arena-fc-runner:latest "$ctx" >/dev/null

# seccomp: Docker default (pinned) + pivot_root for the jailer.
python3 - "$DEPS/dl/docker-default-seccomp.json" "$DEPS/images/fc-runner-seccomp.json" <<'PY'
import json, sys
src, dst = sys.argv[1], sys.argv[2]
d = json.load(open(src))
d["syscalls"].append({
    "names": ["pivot_root"],
    "action": "SCMP_ACT_ALLOW",
    "includes": {"caps": ["CAP_SYS_ADMIN"]},
    "comment": "arena: jailer pivot_root()s into the Firecracker chroot",
})
json.dump(d, open(dst, "w"), indent=1, sort_keys=True)
PY
id=$(docker image inspect "$tag" --format '{{.Id}}')
echo "$id" > "$DEPS/images/fc-runner.image"
echo "$tag $id" >&2
echo "$id"
