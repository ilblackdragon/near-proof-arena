#!/usr/bin/env bash
# Generate a domain-D2 difftest corpus with nearcore's own code (`gen --domain d2`), one
# process per chain (chains are independent and byte-reproducible from (seed, chain index)),
# then merge the per-chain outputs into OUT/{d2,ood,mutants} and write OUT/summary.json last.
#
#   OUT=/path SEED=6262 CHAINS=14 BLOCKS=200 LONG="2 7 12" LONG_BLOCKS=270 PAR=4 \
#     MUTATE_EVERY=14 OOD_CAP=15 DROP_CAP=96 [KEEP_EVERY=1] [CLEAN_PARTS=0] \
#     oracle/scripts/gen-d2-corpus.sh
#
# Chains of at least 250 blocks call the yield contract early, so their yields time out
# inside the chain (yield_timeout_length_in_blocks = 200). A chain whose run fails is
# reported and skipped by the merge (rerun it: finished chains are kept).
#
# RAYON_NUM_THREADS is raised: the TestEnv validates many witnesses concurrently on rayon's
# global pool while wasmtime compiles the test contract with nested rayon jobs on the same
# pool; with a pool as small as the CPU set the run can starve (all workers blocked).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
bin="${BIN:-$here/v3-d1/target/debug/near-arena-oracle-v3-d1}"
OUT="${OUT:?set OUT}"
SEED="${SEED:-6262}"
CHAINS="${CHAINS:-14}"
BLOCKS="${BLOCKS:-200}"
LONG="${LONG:-2 7 12}"
LONG_BLOCKS="${LONG_BLOCKS:-270}"
PAR="${PAR:-4}"
MUTATE_EVERY="${MUTATE_EVERY:-14}"
OOD_CAP="${OOD_CAP:-15}"
DROP_CAP="${DROP_CAP:-96}"
KEEP_EVERY="${KEEP_EVERY:-1}"
CLEAN_PARTS="${CLEAN_PARTS:-0}"
HEAVY="${HEAVY:-/data/illia/nearproof-deps/bin/heavy}"
mkdir -p "$OUT/parts"
rm -f "$OUT/summary.json"
export bin OUT SEED MUTATE_EVERY OOD_CAP DROP_CAP KEEP_EVERY HEAVY
for i in $(seq 0 $((CHAINS - 1))); do
  b="$BLOCKS"
  for l in $LONG; do [[ "$l" == "$i" ]] && b="$LONG_BLOCKS"; done
  echo "$i $b"
done | xargs -P "$PAR" -n 2 sh -c '
  i=$0; b=$1; d="$OUT/parts/$i"
  if [ -f "$d/summary.json" ]; then exit 0; fi
  rm -rf "$d"
  RAYON_NUM_THREADS=256 timeout 7200 "$HEAVY" "$bin" gen --domain d2 --seed "$SEED" --out "$d" \
    --first-chain "$i" --chains 1 --blocks "$b" --mutate-every "$MUTATE_EVERY" --ood-cap "$OOD_CAP" --drop-cap "$DROP_CAP" --keep-every "$KEEP_EVERY" \
    > "$OUT/parts/$i.log" 2>&1 || echo "chain $i failed (see $OUT/parts/$i.log)" >&2
'
python3 - "$OUT" <<'EOF'
import json, os, shutil, sys
out = sys.argv[1]
parts = os.path.join(out, "parts")
merged = None
for i in sorted((int(x) for x in os.listdir(parts) if x.isdigit())):
    d = os.path.join(parts, str(i))
    sp = os.path.join(d, "summary.json")
    if not os.path.exists(sp):
        print("chain %d incomplete, skipped" % i, file=sys.stderr)
        continue
    s = json.load(open(sp))
    for sub in ("d2", "ood", "mutants"):
        src = os.path.join(d, sub)
        if os.path.isdir(src):
            os.makedirs(os.path.join(out, sub), exist_ok=True)
            for c in os.listdir(src):
                dst = os.path.join(out, sub, c)
                if not os.path.exists(dst):
                    shutil.move(os.path.join(src, c), dst)
    if merged is None:
        merged = dict(s)
        merged["chains"] = list(s["chains"])
        merged["d2_violation_counts"] = dict(s["d2_violation_counts"])
    else:
        merged["chains"] += s["chains"]
        for k in ("honest_witnesses", "honest_accepted_by_nearcore", "d2_cases", "d1_cases_among_d2",
                  "d0_cases_among_d2", "ood_cases_written", "mutants", "crafted_transactions"):
            merged[k] += s[k]
        for k, v in s["d2_violation_counts"].items():
            merged["d2_violation_counts"][k] = merged["d2_violation_counts"].get(k, 0) + v
merged["cases_on_disk"] = {sub: len(os.listdir(os.path.join(out, sub))) for sub in ("d2", "ood", "mutants")
                           if os.path.isdir(os.path.join(out, sub))}
json.dump(merged, open(os.path.join(out, "summary.json.tmp"), "w"), indent=2)
os.replace(os.path.join(out, "summary.json.tmp"), os.path.join(out, "summary.json"))
print(json.dumps({k: v for k, v in merged.items() if k != "chains"}, indent=1))
EOF
if [[ "$CLEAN_PARTS" == 1 ]]; then rm -rf "$OUT/parts"; fi
