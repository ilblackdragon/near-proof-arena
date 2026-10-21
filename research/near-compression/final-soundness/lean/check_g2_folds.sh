#!/usr/bin/env bash
# Recheck the measured FINAL's 13 selected scalar fold certificates and transfers.
# Usage: check_g2_folds.sh <ArkLib checkout> <external build directory>
# This is not an end-to-end soundness gate.
set -euo pipefail
ARKLIB=$(cd "${1:?ArkLib checkout}" && pwd)
mkdir -p "${2:?external build directory}"
BUILD=$(cd "$2" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
EXPECTED=a5aa2677fee4e3a79d6bb05136631cce4a08587d
[ "$(git -C "$ARKLIB" rev-parse HEAD)" = "$EXPECTED" ]
git -C "$ARKLIB" diff --quiet HEAD
CPUSET=${CPUSET:-8-15,24-31}
HEAVY=/data/illia/nearproof-deps/bin/heavy
for kind in certs transfers; do
  if [ "$kind" = certs ]; then target=DKTG2FoldCerts; else target=DKTG2FoldTransfer; fi
  python3 "$HERE/../calc/g2_fold_certificates.py" "$kind" > "$BUILD/$target.generated.lean"
  cmp "$BUILD/$target.generated.lean" "$HERE/$target.lean"
done
cd "$ARKLIB"
env HEAVY_MEM=8G taskset -c "$CPUSET" "$HEAVY" lake build \
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.BinaryFoldAgreement \
  > "$BUILD/dependencies.log" 2>&1
for module in DKTG2FoldCerts DKTWhirFold DKTG2FoldTransfer; do
  env LEAN_PATH="$BUILD${LEAN_PATH:+:$LEAN_PATH}" HEAVY_MEM=24G taskset -c "$CPUSET" "$HEAVY" \
    lake env lean -R "$HERE" -o "$BUILD/$module.olean" "$HERE/$module.lean" \
    > "$BUILD/$module.log" 2>&1
done
python3 - "$BUILD" <<'PY'
from pathlib import Path
import re, sys
root = Path(sys.argv[1])
expected = {
    'DKTG2FoldCerts': {f'DKTG2FoldCerts.mca{i}' for i in range(13)},
    'DKTWhirFold': {'DKTWhirFold.backendFold_eq', 'DKTWhirFold.primitiveSquareDomain', 'DKTWhirFold.cosetMajorSquareDomain'},
    'DKTG2FoldTransfer': {f'DKTG2FoldTransfer.final_r{r}_s{s}'
                        for r, count in enumerate([1, 4, 4, 4]) for s in range(1, count+1)}
                        | {'DKTG2FoldTransfer.finalScalarFoldBudget_fraction_lt'},
}
for module, names in expected.items():
    text = (root / f'{module}.log').read_text()
    audits = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    assert set(audits) == names, (module, names - audits.keys())
    for name, axioms in audits.items():
        assert set(axioms.split(', ')) <= {'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    print(f'{module}: checked {len(names)} declarations; kernel axiom audit PASS')
PY
