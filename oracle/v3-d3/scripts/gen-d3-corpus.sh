#!/usr/bin/env bash
# Generate a domain-D3α corpus (`near-arena-oracle-v3-d3 gen --domain d3`), one process per
# chain (chains are independent and byte-reproducible from (seed, chain index)), then merge the
# per-chain outputs into OUT/{d3,ood,mutants} and write OUT/summary.json last.
#
#   OUT=/path SEED=7 CHAINS=8 BLOCKS=200 PAR=1 MUTATE_EVERY=20 CODE_MUTANT_P=0.25 \
#     OOD_CAP=25 DROP_CAP=48 [CHAIN_LIST="0 2 3"] [CLEAN_PARTS=1] oracle/v3-d3/scripts/gen-d3-corpus.sh
#
# Each chain runs under `taskset -c $CPUS $HEAVY` (default CPUs 8-15,24-31). RAYON_NUM_THREADS
# is raised as for D2 (gen-d2-corpus.sh): the TestEnv validates witnesses on rayon's global pool
# while wasmtime compiles with nested rayon jobs. A chain whose run fails is reported and
# skipped by the merge (rerun it: finished chains are kept).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
bin="${BIN:-$here/../d3-ttn/target/debug/near-arena-oracle-v3-d3}"
OUT="${OUT:?set OUT}"
SEED="${SEED:-7}"
CHAINS="${CHAINS:-8}"
BLOCKS="${BLOCKS:-200}"
PAR="${PAR:-1}"
MUTATE_EVERY="${MUTATE_EVERY:-20}"
CODE_MUTANT_P="${CODE_MUTANT_P:-0.25}"
OOD_CAP="${OOD_CAP:-25}"
DROP_CAP="${DROP_CAP:-48}"
CLEAN_PARTS="${CLEAN_PARTS:-0}"
CPUS="${CPUS:-8-15,24-31}"
HEAVY="${HEAVY:-/data/illia/nearproof-deps/bin/heavy}"
mkdir -p "$OUT/parts"
rm -f "$OUT/summary.json"
export bin OUT SEED BLOCKS MUTATE_EVERY CODE_MUTANT_P OOD_CAP DROP_CAP HEAVY CPUS
CHAIN_LIST="${CHAIN_LIST:-$(seq 0 $((CHAINS - 1)))}"
for i in $CHAIN_LIST; do echo "$i"; done | xargs -P "$PAR" -n 1 sh -c '
  i=$0; d="$OUT/parts/$i"
  if [ -f "$d/summary.json" ]; then exit 0; fi
  rm -rf "$d"
  RAYON_NUM_THREADS=256 timeout 10800 taskset -c "$CPUS" "$HEAVY" "$bin" gen --domain d3 --seed "$SEED" --out "$d" \
    --first-chain "$i" --chains 1 --blocks "$BLOCKS" --mutate-every "$MUTATE_EVERY" --code-mutant-p "$CODE_MUTANT_P" \
    --ood-cap "$OOD_CAP" --drop-cap "$DROP_CAP" > "$OUT/parts/$i.log" 2>&1 || echo "chain $i failed (see $OUT/parts/$i.log)" >&2
'
python3 - "$OUT" <<'PY'
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
    for sub in ("d3", "ood", "mutants"):
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
        merged["d3_violation_counts"] = dict(s["d3_violation_counts"])
        merged["d3"] = dict(s["d3"])
    else:
        merged["chains"] += s["chains"]
        for k in ("honest_witnesses", "honest_accepted_by_nearcore", "d3_cases", "d1_cases_among_d3",
                  "d0_cases_among_d3", "ood_cases_written", "mutants", "crafted_transactions"):
            merged[k] += s[k]
        for key in ("d3_violation_counts", "d3"):
            for k, v in s[key].items():
                merged[key][k] = merged[key].get(k, 0) + v
merged["cases_on_disk"] = {sub: len(os.listdir(os.path.join(out, sub))) for sub in ("d3", "ood", "mutants")
                           if os.path.isdir(os.path.join(out, sub))}
json.dump(merged, open(os.path.join(out, "summary.json.tmp"), "w"), indent=2, sort_keys=True)
os.replace(os.path.join(out, "summary.json.tmp"), os.path.join(out, "summary.json"))
print(json.dumps({k: v for k, v in merged.items() if k not in ("chains", "d3")}, indent=1))
PY
if [[ "$CLEAN_PARTS" == 1 ]]; then rm -rf "$OUT/parts"; fi
