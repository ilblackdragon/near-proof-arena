#!/usr/bin/env bash
# Regenerate the v3 (near/pv86/chunk-validation/v0) fixtures with nearcore's own code.
# Byte-reproducible: FakeClock + fixed genesis time + seeded RNG (oracle/v3/src/chaingen.rs).
#   public set (committed):  oracle/fixtures/v3/public   (seed 4243, 2 chains x 40 blocks)
#   full difftest set:       $OUT (default /tmp/near-v3-full; seed 4243, 8 chains x 120 blocks)
#   leaf vectors (committed): oracle/fixtures/v3/vectors (seed 86)
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
"$here/scripts/link-nearcore.sh" >/dev/null
(cd "$here/v3" && cargo build -j "${JOBS:-16}")
bin="$here/v3/target/debug/near-arena-oracle-v3"
rm -rf "$here/fixtures/v3/public"
"$bin" gen --seed 4243 --out "$here/fixtures/v3/public" --chains 2 --blocks 40 --mutate-every 25 --ood-cap 1
"$bin" vectors --out "$here/fixtures/v3/vectors" --seed 86
if [[ "${FULL:-0}" == 1 ]]; then
  OUT="${OUT:-/tmp/near-v3-full}"
  rm -rf "$OUT"
  "$bin" gen --seed 4243 --out "$OUT" --chains 8 --blocks 120 --mutate-every 6
fi
