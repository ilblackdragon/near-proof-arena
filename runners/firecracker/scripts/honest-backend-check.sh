#!/usr/bin/env bash
# False-positive check for seccomp violation detection on a real backend:
# build the package in a Firecracker VM with the pinned toolchain image
# (policy `tooling`), then run prepare + prove + verify on N public oracle
# fixtures in fresh VMs (policy `strict`). Fails if any step reports a
# sandbox violation or a non-zero exit.
#
#   honest-backend-check.sh PKG_DIR TOOLCHAIN_DIGEST_HEX [N_CASES=2] [MEM_MB=8192] [CPUS=8-15]
#
# PKG_DIR must contain source/vendor (run the package's vendor step first).
set -euo pipefail
PKG=$(cd "$1" && pwd); TC=$2; N=${3:-2}; MEM=${4:-8192}; CPUS=${5:-8,9,10,11,12,13,14,15}
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
FIX=${FIXTURES:-$REPO/oracle/fixtures/public}
TCDIR=${ARENA_TOOLCHAIN_IMAGES:-/data/illia/nearproof-deps/toolchain-images}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/honest-check.XXXXXX")
trap 'rm -rf "$WORK"' EXIT
RUN="$REPO/target/release/arena-fc-run"
(cd "$REPO" && cargo build -q --release -p arena-firecracker --bin arena-fc-run)
TC_PATH=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["env"]["PATH"])' "$TCDIR/$TC.json")
name=$(basename "$PKG")

check() { # label json
  python3 - "$1" "$2" <<'PY'
import json, sys
label, path = sys.argv[1], sys.argv[2]
d = json.load(open(path))
v = d.get("violations", [])
ex = d["exit"]
print(f"{label:28} exit={ex} wall={d['wall_ns']/1e9:8.2f}s violations={v}")
if v or ex != {"kind": "exited", "value": 0}:
    print(d.get("stderr_trunc", "")[-2000:])
    sys.exit(1)
PY
}

# 1. build (tooling policy, toolchain image as root)
mkdir -p "$WORK/pkg"
tar -C "$PKG" --exclude=./out --exclude=./source/target -cf - . | tar -C "$WORK/pkg" -xf -
"$RUN" --policy tooling --root-image "$TCDIR/$TC" --mem-mb "$MEM" --scratch-mb 32768 --timeout-s 3600 \
  --cpus "$CPUS" --pids 4096 --env "PATH=$TC_PATH" --env SOURCE_DATE_EPOCH=0 --env CARGO_NET_OFFLINE=true \
  --ro "$WORK/pkg:/in/pkg" --copy-in /in/pkg:work --cwd /scratch/work --mkdir tmp \
  --collect work/out --out "$WORK/build" -- /bin/bash build-recipe/build.sh > "$WORK/build.json"
check "$name build" "$WORK/build.json"
BUNDLE="$WORK/build/work/out"

# 2. prepare
"$RUN" --mem-mb "$MEM" --scratch-mb 4096 --timeout-s 600 --cpus "$CPUS" \
  --ro "$BUNDLE:/in/bundle" --ro "$FIX/params.bin:/in/params.bin" --mkdir out/public --collect out \
  --out "$WORK/prep" -- /in/bundle/prepare --params /in/params.bin --out /scratch/out/public > "$WORK/prep.json"
check "$name prepare" "$WORK/prep.json"

# 3. prove + verify on N fixtures
i=0
for c in $(ls "$FIX/cases" | head -n "$N"); do
  i=$((i + 1))
  "$RUN" --mem-mb "$MEM" --scratch-mb 8192 --timeout-s 1800 --cpus "$CPUS" --pids 4096 \
    --ro "$BUNDLE:/in/bundle" --ro "$WORK/prep/out/public:/in/public" \
    --ro "$FIX/cases/$c/request.bin:/in/request.bin" --ro "$FIX/cases/$c/witness.bin:/in/witness.bin" \
    --mkdir out --collect out --out "$WORK/prove$i" -- /in/bundle/prove --public /in/public \
    --request /in/request.bin --witness /in/witness.bin --claim-out /scratch/out/claim.bin \
    --proof-out /scratch/out/proof.bin > "$WORK/prove$i.json"
  check "$name prove $c" "$WORK/prove$i.json"
  cmp -s "$WORK/prove$i/out/claim.bin" "$FIX/cases/$c/expected_claim.bin" && echo "  claim == expected" \
    || { echo "  claim differs from expected"; exit 1; }
  "$RUN" --mem-mb "$MEM" --scratch-mb 1024 --timeout-s 600 --cpus "$CPUS" \
    --ro "$BUNDLE:/in/bundle" --ro "$WORK/prep/out/public:/in/public" \
    --ro "$WORK/prove$i/out/claim.bin:/in/claim.bin" --ro "$WORK/prove$i/out/proof.bin:/in/proof.bin" \
    -- /in/bundle/verify --public /in/public --claim /in/claim.bin --proof /in/proof.bin > "$WORK/verify$i.json"
  check "$name verify $c" "$WORK/verify$i.json"
done
echo "OK: $name honest run clean (no sandbox violations)"
