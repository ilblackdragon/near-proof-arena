#!/usr/bin/env bash
# Generate the HELD-OUT workload set for near-chunk-validation-d0
# (near/pv86/chunk-validation/v0, domain D0) from a secret seed. Only the
# TreeDigest of the output is committed (spec/challenge-inputs/heldout-commitment-v3-d0.json);
# the seed and the cases stay off-repo until the season ends.
#   gen-heldout-v3.sh <seed-file> <out-dir> [nearspec-v3-check]
# The seed file holds one decimal u64; create it with
#   python3 -c 'import secrets;print(secrets.randbits(62))' > SEED && chmod 600 SEED
# Layout (runners/worker NearV3Oracle):
#   <class>/{params.bin, cases/<n>/{request,witness,expected_claim}.bin + meta.json}   24 per class,
#     generated with the class's generator-spec args (spec/workloads/near-chunk-validation-d0)
#   rejections/<n>/{request,witness}.bin + meta.json   64 (32 out-of-D0 honest chunks, 32
#     nearcore-rejected mutants) from 2 chains of the judge's rejection-sampling recipe
# With a compiled nearspec-v3-check, every case is also re-checked by the Lean relation.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/.." && pwd)"
seed="$(tr -d '[:space:]' < "$1")"; out="$2"; lean_check="${3:-}"
bin="$here/v3/target/debug/near-arena-oracle-v3"
rm -rf "$out"; mkdir -p "$out"
k=0
for cls in d0-quiet d0-transfers d0-missing; do
  mapfile -t args < <(python3 -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["args"]))' \
    "$repo/spec/workloads/near-chunk-validation-d0/$cls.json")
  "$bin" gen --seed $((seed + k)) --out "$out/$cls" "${args[@]}" --d0-target 24 2>/dev/null
  rm -f "$out/$cls/summary.json"
  python3 "$repo/spec/tools/params_bin_v3.py" "$out/$cls/params.bin" D0 >/dev/null
  k=$((k + 1))
done
tmp="$out/.rej"
"$bin" gen --seed $((seed + k)) --out "$tmp" --fixtures-layout --no-positives --rotate \
  --mutate-every 3 --ood-cap 3 --chains 2 --blocks 40 2>/dev/null
python3 - "$tmp/rejections" "$out/rejections" "$seed" <<'PY'
import json, os, random, shutil, sys
src, dst, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
kinds = {"honest": [], "mutant": []}
for n in sorted(os.listdir(src)):
    kinds[json.load(open(os.path.join(src, n, "meta.json")))["kind"]].append(n)
rng = random.Random(seed)
os.makedirs(dst)
for k, names in kinds.items():
    rng.shuffle(names)
    for n in names[:32]:
        shutil.copytree(os.path.join(src, n), os.path.join(dst, n))
print({k: min(32, len(v)) for k, v in kinds.items()}, file=sys.stderr)
PY
rm -rf "$tmp"
if [ -n "$lean_check" ]; then
  chk="$(mktemp -d)"
  for d in "$out"/*/cases/* "$out"/rejections/*; do
    t="$chk/$(basename "$(dirname "$(dirname "$d")")")-$(basename "$(dirname "$d")")-$(basename "$d")"
    mkdir -p "$t"; ln -s "$d/request.bin" "$t/claim.bin"; ln -s "$d/witness.bin" "$t/witness.bin"
  done
  pos=$("$lean_check" "$chk"/*-cases-* | grep -c '"verdict": "accept"')
  neg=$("$lean_check" "$chk"/*-rejections-* | grep -c '"verdict": "accept"' || true)
  rm -rf "$chk"
  echo "Lean relation: $pos/72 positives accepted, $neg rejections accepted (must be 0)"
fi
echo "held-out set written to $out"
