#!/usr/bin/env bash
# Recheck the measured G2 fold certificates/transfers and the WHIR-transfer companion files.
# Usage: check_g2_folds.sh <ArkLib checkout> <external build directory>
# This is not an end-to-end soundness gate.
set -euo pipefail
ARKLIB=$(cd "${1:?ArkLib checkout}" && pwd)
mkdir -p "${2:?external build directory}"
BUILD=$(cd "$2" && pwd)
HERE=$(cd "$(dirname "$0")" && pwd)
CALC=$(cd "$HERE/../calc" && pwd)
EXPECTED=a5aa2677fee4e3a79d6bb05136631cce4a08587d
[ "$(git -C "$ARKLIB" rev-parse HEAD)" = "$EXPECTED" ]
git -C "$ARKLIB" diff --quiet HEAD
CPUSET=${CPUSET:-8-15,24-31}
HEAVY=/data/illia/nearproof-deps/bin/heavy

# 1. Byte-identical regeneration of every generated Lean file.
for spec in g2_fold_certificates:certs:DKTG2FoldCerts \
            g2_fold_certificates:transfers:DKTG2FoldTransfer \
            g2_fold_coverage:certs:DKTG2FoldCoverageCerts \
            g2_fold_coverage:transfers:DKTG2FoldCoverage; do
  IFS=: read -r script kind target <<< "$spec"
  (cd "$CALC" && python3 "$script.py" "$kind") > "$BUILD/$target.generated.lean"
  cmp "$BUILD/$target.generated.lean" "$HERE/$target.lean"
done

cd "$ARKLIB"
env HEAVY_MEM=8G taskset -c "$CPUSET" "$HEAVY" lake build \
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.BinaryFoldAgreement \
  > "$BUILD/dependencies.log" 2>&1

# 2. Build every checked module, recording exit codes.
declare -A EXITCODE
for module in DKTG2FoldCerts DKTWhirFold DKTG2FoldTransfer \
              DKTAdaptive DKTOrderedCoset DKTG2FoldCoverageCerts DKTG2FoldCoverage \
              DKTRoundCompose; do
  if env LEAN_PATH="$BUILD${LEAN_PATH:+:$LEAN_PATH}" HEAVY_MEM=24G taskset -c "$CPUSET" "$HEAVY" \
      lake env lean -R "$HERE" -o "$BUILD/$module.olean" "$HERE/$module.lean" \
      > "$BUILD/$module.log" 2>&1; then
    EXITCODE[$module]=0
  else
    EXITCODE[$module]=$?
  fi
  echo "$module exit=${EXITCODE[$module]}"
done

# 3. Axiom audit, including every newly added declaration.
python3 - "$BUILD" <<'PY'
from pathlib import Path
import re, sys
root = Path(sys.argv[1])
final13 = {f'DKTG2FoldTransfer.final_r{r}_s{s}'
           for r, count in enumerate([1, 4, 4, 4]) for s in range(1, count + 1)}
coverage = {f'DKTG2FoldCoverage.{role}_r{r}_s{s}'
            for role, rounds in (('final', [1, 4, 4, 4]), ('parent', [None, 4, 4, None]))
            for r, count in enumerate(rounds) if count for s in range(0, count + 1)}
expected = {
    'DKTG2FoldCerts': {f'DKTG2FoldCerts.mca{i}' for i in range(13)},
    'DKTWhirFold': {'DKTWhirFold.backendFold_eq', 'DKTWhirFold.primitiveSquareDomain',
                    'DKTWhirFold.cosetMajorSquareDomain'},
    'DKTG2FoldTransfer': final13 | {'DKTG2FoldTransfer.finalScalarFoldBudget_fraction_lt'},
    'DKTAdaptive': {'DKTAdaptive.notMem_badRuns_iff_allGood',
                    'DKTAdaptive.badRuns_probability',
                    'DKTAdaptive.badRuns_probability_const',
                    'DKTAdaptive.allGood_probability',
                    'DKTAdaptive.badOfWord_bound'},
    'DKTOrderedCoset': {'DKTOrderedCoset.fifteenRoot_eq',
                        'DKTOrderedCoset.fieldGenerator_isPrimitive',
                        'DKTOrderedCoset.fifteenRoot_isPrimitive',
                        'DKTOrderedCoset.two_adic_half_turn',
                        'DKTOrderedCoset.cosetIndex_decomp',
                        'DKTOrderedCoset.roots_eq_cosetMajor',
                        'DKTOrderedCoset.deployedSquareDomain'},
    'DKTG2FoldCoverageCerts': {f'DKTG2FoldCoverageCerts.mca{i}' for i in range(14)},
    'DKTG2FoldCoverage': coverage | {'DKTG2FoldCoverage.coverageFoldBudget_sum'},
    'DKTRoundCompose': {'DKTRoundCompose.roundFold_probability',
                        'DKTRoundCompose.roundFold_probability_empty',
                        'DKTRoundCompose.roundFold_probability_uniform',
                        'DKTRoundCompose.roundGood_probability',
                        'DKTRoundCompose.stepBudgets_of_certificates'},
}
ok = True
for module, names in expected.items():
    text = (root / f'{module}.log').read_text()
    audits = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text))
    # `decide`/`norm_num` proofs can print "does not depend on any axioms"; treat as empty.
    for name in re.findall(r"^'([^']+)' does not depend on any axioms$", text, re.M):
        audits.setdefault(name, '')
    if set(audits) != names:
        print(f'{module}: MISSING {sorted(names - audits.keys())} '
              f'EXTRA {sorted(audits.keys() - names)}')
        ok = False
        continue
    bad = {n: a for n, a in audits.items()
           if not set(a.strip() for a in a.split(',') if a.strip()) <=
           {'propext', 'Classical.choice', 'Quot.sound'}}
    if bad:
        print(f'{module}: FORBIDDEN AXIOMS {bad}')
        ok = False
        continue
    print(f'{module}: checked {len(names)} declarations; kernel axiom audit PASS')
sys.exit(0 if ok else 1)
PY

# 4. No forbidden constructs anywhere in the checked files.
if grep -nE '\b(sorry|native_decide|implemented_by)\b' \
    "$HERE"/DKTAdaptive.lean "$HERE"/DKTOrderedCoset.lean \
    "$HERE"/DKTG2FoldCoverage.lean "$HERE"/DKTG2FoldCoverageCerts.lean \
    "$HERE"/DKTRoundCompose.lean; then
  echo "FORBIDDEN CONSTRUCT" >&2
  exit 1
fi
echo "no sorry / native_decide / implemented_by in the new modules"
