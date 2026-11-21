#!/usr/bin/env bash
# The mutant batteries under pycheck.py (no proving): pymutants.sh CASE OUT [final|init]
# For each mutant: tracegen at the class template, then the Python precheck + statement check.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CASE=$1; OUT=$2; T=${3:-final}
TOOL=$HERE/lean/.lake/build/bin/m5d-tool
mkdir -p "$OUT"
"$TOOL" dump "$CASE" "$OUT/dump.json" > /dev/null
"$TOOL" air-$T "$OUT/$T.json" "$OUT/$T-names.json" > /dev/null
TM=$HERE/templates/F1.json; LIST=MUTANTS
[ "$T" = init ] && { TM=$HERE/templates/INIT-14.json; LIST=INIT_MUTANTS; }
gen() { python3 "$HERE/tracegen.py" "$OUT/dump.json" "$OUT/$T-names.json" "$1" --template "$TM" "${@:2}"; }
gen "$OUT/honest" > /dev/null
echo "honest: $(python3 "$HERE/pycheck.py" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/honest" | tail -1)"
rm -rf "$OUT/honest"
ALL=$(python3 -c "import sys; sys.path.insert(0, '$HERE'); import tracegen; print(' '.join(tracegen.$LIST))")
for m in ${MUTANTS:-$ALL}; do
  rc=0; gen "$OUT/mut" --mutant "$m" > "$OUT/mut.gen.txt" 2>&1 || rc=$?
  if [ "$rc" = 3 ]; then echo "$m: NOT APPLICABLE"; continue; fi
  [ "$rc" = 0 ] || { echo "$m: tracegen failed (exit $rc): $(tail -1 "$OUT/mut.gen.txt")"; continue; }
  r=$(python3 "$HERE/pycheck.py" "$OUT/$T.json" "$OUT/$T-names.json" "$OUT/mut" 2>&1 | tr '\n' ' ' | cut -c1-230) || true
  echo "$m: $r"
  rm -rf "$OUT/mut"
done
