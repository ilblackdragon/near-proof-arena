#!/usr/bin/env bash
# Point oracle/vendor/nearcore at a checkout of the pinned nearcore commit.
# Usage: scripts/link-nearcore.sh [/path/to/nearcore]   (default: /data/illia/nearproof-deps/nearcore)
# Refuses to link a checkout whose HEAD is not the commit recorded in NEARCORE_PIN.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
src="${1:-/data/illia/nearproof-deps/nearcore}"
want="$(sed -n 's/^commit=//p' "$here/NEARCORE_PIN")"
have="$(git -C "$src" rev-parse HEAD)"
if [[ "$have" != "$want" ]]; then
  echo "nearcore checkout $src is at $have, expected $want (NEARCORE_PIN)" >&2
  exit 1
fi
if [[ -n "$(git -C "$src" status --porcelain --untracked-files=no)" ]]; then
  echo "nearcore checkout $src has local modifications; refusing" >&2
  exit 1
fi
mkdir -p "$here/vendor"
ln -sfn "$src" "$here/vendor/nearcore"
echo "linked $here/vendor/nearcore -> $src ($have)"
