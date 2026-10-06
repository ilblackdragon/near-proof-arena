#!/usr/bin/env bash
# Gate of the PROVER-ONLY child (run from the repo, heavy wrapper + CPUs 8-15,24-31):
#   tools/byte-match.sh          cargo test: native prove == source/tests/lean-prover.sha256
#   tools/byte-match.sh --regen  rebuild the PARENT (examples/reexec-v3-d0) with its build
#                                recipe, run its Lean prover on every public positive and
#                                rewrite the manifest, then run the test
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(cd "$HERE/../.." && pwd)"
HEAVY="${HEAVY:-/data/illia/nearproof-deps/bin/heavy}"
CPUS="${CPUS:-8-15,24-31}"
if [ "${1:-}" = "--regen" ]; then
  tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
  git -C "$REPO" archive --format=tar HEAD examples/reexec-v3-d0 | tar -x -C "$tmp"
  ( cd "$tmp/examples/reexec-v3-d0" && taskset -c "$CPUS" "$HEAVY" bash build-recipe/build.sh >/dev/null )
  L="$tmp/examples/reexec-v3-d0/out/prove"
  mkdir -p "$tmp/pub" "$tmp/o"
  : >"$HERE/source/tests/lean-prover.sha256"
  for d in "$REPO"/oracle/fixtures/v3/arena-public/cases/*; do
    taskset -c "$CPUS" "$L" --public "$tmp/pub" --request "$d/request.bin" --witness "$d/witness.bin" \
      --claim-out "$tmp/o/claim.bin" --proof-out "$tmp/o/proof.bin"
    echo "$(sha256sum <"$tmp/o/proof.bin" | cut -c1-64)  $(basename "$d")" >>"$HERE/source/tests/lean-prover.sha256"
  done
fi
cd "$HERE/source"
taskset -c "$CPUS" "$HEAVY" cargo test --release --locked --offline --test byte_match
