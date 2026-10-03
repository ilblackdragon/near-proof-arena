#!/usr/bin/env bash
# Generate the HELD-OUT workload set for near-transfer-receipt-v1 from a secret
# seed. Only the TreeDigest of the output is committed (workload_suite.heldout_commitment);
# the seed and the cases stay off-repo until the season ends.
#   gen-heldout.sh <seed-file> <out-dir>
# The seed file holds one decimal u64; create it with
#   python3 -c 'import secrets;print(secrets.randbits(64))' > SEED && chmod 600 SEED
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
seed="$(tr -d '[:space:]' < "$1")"; out="$2"
bin="$here/target/debug/near-arena-oracle"
rm -rf "$out"; mkdir -p "$out"
for r in 1 16 256; do
  "$bin" gen --seed "$seed" --valid 24 --receipts "$r" --fixtures-layout --out "$out/batch-$r" >/dev/null
done
python3 "$here/tools/spec_check.py" "$out" >/dev/null
echo "held-out set written to $out"
