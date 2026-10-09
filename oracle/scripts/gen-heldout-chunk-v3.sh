#!/usr/bin/env bash
# Generate the HELD-OUT workload set of near-chunk-v3 (one combined set over the tiers D0..D3a)
# from a secret seed. Only the TreeDigest of the output is committed
# (spec/challenge-inputs/heldout-commitment-chunk-v3.json); the seed and the cases stay off-repo until
# the season ends.
#   gen-heldout-chunk-v3.sh <seed-file> <out-dir> [nearspec-v3-check-d3]
# The seed file holds one decimal u64; create it with
#   python3 -c 'import secrets;print(secrets.randbits(62))' > SEED && chmod 600 SEED
# Layout (runners/worker NearV3Oracle):
#   <class>/{params.bin, cases/<n>/{request,witness,expected_claim}.bin + meta.json}   16 per class,
#     generated with the class's generator spec (spec/workloads/near-chunk-validation-d0 for d0-*,
#     spec/workloads/near-chunk-v3 for the others), params.bin domain D3a
#   rejections/<n>/{request,witness}.bin + meta.json   64: 24 out-of-D3α honest chunks and 24
#     nearcore-rejected D3 mutants (a D3 run of the judge's rejection recipe), 8 + 8 nearcore-rejected
#     D1 / D2 mutants (false claims at every tier)
# With a compiled nearspec-v3-check-d3 every case is re-checked by the statement's top rung.
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
repo="$(cd "$here/.." && pwd)"
seed="$(tr -d '[:space:]' < "$1")"; out="$2"; lean_check="${3:-}"
[ -z "$lean_check" ] || lean_check="$(cd "$(dirname "$lean_check")" && pwd)/$(basename "$lean_check")"
b0="${BIN_D0:-/data/illia/nearproof-live/bin/near-arena-oracle-v3}"   # oracle/v3 at the D0 specs' pinned source
b1="${BIN_D1:-$here/d3-ttn/target/debug/near-arena-oracle-v3-d1}"
b3="${BIN_D3:-$here/d3-ttn/target/debug/near-arena-oracle-v3-d3}"
N=16
rm -rf "$out"; mkdir -p "$out"
k=0
spec_args() { python3 -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["args"]))' "$1"; }
for cls in d0-quiet d0-transfers d0-missing d1-transfers d1-mixed d1-receipts d2-actions d2-queues d2-epoch \
           d3-calls d3-callbacks d3-nonwasm d3-maxgas; do
  case "$cls" in
    d0-*) bin="$b0"; spec="$repo/spec/workloads/near-chunk-validation-d0/$cls.json";;
    d1-*|d2-*) bin="$b1"; spec="$repo/spec/workloads/near-chunk-v3/$cls.json";;
    d3-*) bin="$b3"; spec="$repo/spec/workloads/near-chunk-v3/$cls.json";;
  esac
  mapfile -t args < <(spec_args "$spec")
  RAYON_NUM_THREADS=256 "$bin" gen --seed $((seed + k)) --out "$out/$cls" "${args[@]}" --d0-target $N >/dev/null 2>&1 \
    || { echo "class $cls: generator failed" >&2; exit 1; }
  rm -rf "$out/$cls/summary.json" "$out/$cls/rejections"
  python3 "$repo/spec/tools/params_bin_v3.py" "$out/$cls/params.bin" D3a >/dev/null
  k=$((k + 1))
done
tmp="$out/.rej"; rm -rf "$tmp"
RAYON_NUM_THREADS=256 "$b3" gen --domain d3 --seed $((seed + k)) --out "$tmp/d3" --fixtures-layout --no-positives \
  --chains 2 --blocks 60 --mutate-every 3 --code-mutant-p 0.25 --ood-cap 3 --drop-cap 4 >/dev/null 2>&1
RAYON_NUM_THREADS=256 "$b1" gen --domain d1 --seed $((seed + k + 1)) --out "$tmp/d1" --fixtures-layout --no-positives \
  --rotate --chains 2 --blocks 40 --mutate-every 3 --ood-cap 0 >/dev/null 2>&1
RAYON_NUM_THREADS=256 "$b1" gen --domain d2 --seed $((seed + k + 2)) --out "$tmp/d2" --fixtures-layout --no-positives \
  --chains 2 --blocks 60 --mutate-every 3 --ood-cap 0 --drop-cap 4 >/dev/null 2>&1
python3 - "$tmp" "$out/rejections" "$seed" <<'PY'
import json, os, random, shutil, sys
src, dst, seed = sys.argv[1], sys.argv[2], int(sys.argv[3])
rng = random.Random(seed)
os.makedirs(dst)
def pick(d, kind, n, rejected_only):
    names = []
    for c in sorted(os.listdir(os.path.join(src, d, "rejections"))):
        m = json.load(open(os.path.join(src, d, "rejections", c, "meta.json")))
        if m.get("kind") == kind and (not rejected_only or m.get("nearcore") != "ok"):
            names.append(c)
    rng.shuffle(names)
    for c in names[:n]:
        shutil.copytree(os.path.join(src, d, "rejections", c), os.path.join(dst, f"{d}-{c}"))
    return min(n, len(names))
print({"d3-ood": pick("d3", "honest", 24, False), "d3-mutants": pick("d3", "mutant", 24, False),
       "d1-mutants": pick("d1", "mutant", 8, True), "d2-mutants": pick("d2", "mutant", 8, True)}, file=sys.stderr)
PY
rm -rf "$tmp"
if [ -n "$lean_check" ]; then
  chk="$(mktemp -d "${TMPDIR:-/tmp}/heldout-chk.XXXXXX")"
  for d in "$out"/*/cases/* "$out"/rejections/*; do
    t="$chk/$(basename "$(dirname "$(dirname "$d")")")-$(basename "$(dirname "$d")")-$(basename "$d")"
    mkdir -p "$t"; ln -s "$d/request.bin" "$t/claim.bin"; ln -s "$d/witness.bin" "$t/witness.bin"
  done
  npos=$(ls -d "$chk"/*-cases-* | wc -l)
  pos=$(cd "$chk" && ls -d *-cases-* | xargs -n 50 "$lean_check" | grep -c '"verdict": "accept"')
  neg=$(cd "$chk" && ls -d *-rejections-* | xargs -n 50 "$lean_check" | grep -c '"verdict": "accept"' || true)
  rm -rf "$chk"
  echo "checkD3: $pos/$npos positives accepted, $neg rejections accepted (must be 0)"
fi
echo "held-out set written to $out"
