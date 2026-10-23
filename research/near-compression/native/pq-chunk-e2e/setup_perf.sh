#!/usr/bin/env bash
# Isolated allocation/copy experiment; check all underlying pinned patches first.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
export NEARPROOF_PQ_DEPS=${NEARPROOF_PQ_DEPS:-/data/illia/nearproof-deps/pq-chunk-perf}
D=$NEARPROOF_PQ_DEPS
patches=(stark-backend-unified:perf-buffer-reuse.patch stark-backend-unified:perf-copy-backend.patch openvm-sha384:perf-copy-sha.patch stark-backend-unified:perf-dft-pad.patch)
for ((i=${#patches[@]}-1; i>=0; i--)); do
  IFS=: read -r tree patch <<< "${patches[i]}"
  if git -C "$D/$tree" apply --reverse --check "$HERE/$patch" 2>/dev/null; then
    git -C "$D/$tree" apply --reverse "$HERE/$patch"
  fi
done
"$HERE/setup.sh"
for spec in "${patches[@]}"; do
  IFS=: read -r tree patch <<< "$spec"
  git -C "$D/$tree" apply --check "$HERE/$patch"
  git -C "$D/$tree" apply "$HERE/$patch"
  git -C "$D/$tree" apply --reverse --check "$HERE/$patch"
done
