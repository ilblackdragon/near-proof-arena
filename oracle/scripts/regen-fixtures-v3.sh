#!/usr/bin/env bash
# Regenerate the v3 (near/pv86/chunk-validation/v0) fixtures with nearcore's own code.
# Byte-reproducible: FakeClock + fixed genesis time + seeded RNG (oracle/v3/src/chaingen.rs).
#   public set (committed):  oracle/fixtures/v3/public   (seed 4243, 2 chains x 40 blocks)
#   full difftest set:       $OUT (default /tmp/near-v3-full; seed 4243, 8 chains x 120 blocks)
#   leaf vectors (committed): oracle/fixtures/v3/vectors (seed 86)
#   D1 public set (committed): oracle/fixtures/v3/public-d1 (seed 4243, 2 chains x 40 blocks, --domain d1)
#   D1 full difftest set:      $OUT_D1 (default /tmp/near-v3-d1-full; seed 5151, 12 chains x 150 blocks)
#   Ed25519 vectors (committed): oracle/fixtures/v3/ed25519 (oracle/tools/gen_ed25519_vectors.py, SOURCES.json)
#   D2 public set (committed): oracle/fixtures/v3/public-d2 (seed 4243, chains 0, 3 x 60 blocks and chain 2 x 240
#                              blocks, --domain d2, honest cases kept when they add coverage; difftest.json from
#                              difftest_v3_d2.py)
#   D2 full difftest set:      $OUT_D2 (default /tmp/near-v3-d2-full; seed 6262, 14 chains x 200 blocks,
#                              chains 2/7/12 x 270 blocks; oracle/scripts/gen-d2-corpus.sh)
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
"$here/scripts/link-nearcore.sh" >/dev/null
(cd "$here/v3" && cargo build -j "${JOBS:-16}")
(cd "$here/v3-d1" && cargo build -j "${JOBS:-16}")   # D1 oracle (separate crate; ../v3 stays as pinned)
bin="$here/v3/target/debug/near-arena-oracle-v3"
bin_d1="$here/v3-d1/target/debug/near-arena-oracle-v3-d1"
rm -rf "$here/fixtures/v3/public"
"$bin" gen --seed 4243 --out "$here/fixtures/v3/public" --chains 2 --blocks 40 --mutate-every 25 --ood-cap 1
"$bin" vectors --out "$here/fixtures/v3/vectors" --seed 86
rm -rf "$here/fixtures/v3/public-d1"
"$bin_d1" gen --seed 4243 --out "$here/fixtures/v3/public-d1" --chains 2 --blocks 40 --mutate-every 25 --ood-cap 1 --domain d1
rm -rf "$here/fixtures/v3/public-d2"
OUT="$here/fixtures/v3/public-d2" SEED=4243 CHAIN_LIST="0 2 3" BLOCKS=60 LONG="2" LONG_BLOCKS=240 PAR="${PAR:-4}" \
  MUTATE_EVERY=45 OOD_CAP=1 DROP_CAP=8 KEEP_EVERY=100000 CLEAN_PARTS=1 "$here/scripts/gen-d2-corpus.sh"
python3 "$here/tools/difftest_v3_d2.py" --cases "$here/fixtures/v3/public-d2" --python "$here/tools/spec_check_v3_d2.py" \
  --python-d1 "$here/tools/spec_check_v3_d1.py" --report "$here/fixtures/v3/public-d2/difftest.json" || true
if [[ "${FULL:-0}" == 1 ]]; then
  OUT="${OUT:-/tmp/near-v3-full}"
  rm -rf "$OUT"
  "$bin" gen --seed 4243 --out "$OUT" --chains 8 --blocks 120 --mutate-every 6
  OUT_D1="${OUT_D1:-/tmp/near-v3-d1-full}"
  rm -rf "$OUT_D1"
  "$bin_d1" gen --seed 5151 --out "$OUT_D1" --chains 12 --blocks 150 --ood-cap 40 --mutate-every 4 --domain d1
  OUT_D2="${OUT_D2:-/tmp/near-v3-d2-full}"
  rm -rf "$OUT_D2"
  OUT="$OUT_D2" SEED=6262 CHAINS=14 BLOCKS=200 LONG="2 7 12" LONG_BLOCKS=270 MUTATE_EVERY=14 OOD_CAP=15 DROP_CAP=96 \
    PAR="${PAR:-4}" "$here/scripts/gen-d2-corpus.sh"
fi
