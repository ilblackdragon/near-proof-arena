#!/usr/bin/env bash
# Minimal reference harness for the negative-example suite.
#
# For each negative/NN_*.lean it builds a *judge-generated wrapper*:
#   <candidate imports> + import Toy.Artifacts (judge module)
#   <candidate body>
#   theorem ArenaJudge.check : <expected type> := Candidate.certificate
#   #print axioms ArenaJudge.check
# and rejects on elaboration failure or any axiom outside the allowlist.
# The formal-checker lane implements the production version (isolated
# elaboration, export, independent re-check); this script only demonstrates
# that every negative example is rejected and the positive control passes.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
root="$(dirname "$here")"
export PATH="$HOME/.elan/bin:$PATH"
allow="propext Classical.choice Quot.sound"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
fail=0
cd "$root"
for f in "$here"/[0-9][0-9]_*.lean; do
  name="$(basename "$f" .lean)"
  expect="$(grep -m1 '^-- EXPECT:' "$f" | sed 's/^-- EXPECT: *//')"
  judge="$(grep -m1 '^-- JUDGE:' "$f" | sed 's/^-- JUDGE: *//')"
  [ -z "$judge" ] && judge="ToyJudge.Expected"
  case "$name" in 09_stale_digest) judge="StaleJudge.Expected";; esac
  w="$tmp/$name.lean"
  { grep '^import ' "$f"; echo "import Toy.Artifacts"
    grep -v '^import ' "$f"
    echo; echo "theorem ArenaJudge.check : $judge := Candidate.certificate"
    echo "#print axioms ArenaJudge.check"; } > "$w"
  out="$(lake env lean "$w" 2>&1)"; rc=$?
  verdict=PASS; why=""
  if [ $rc -ne 0 ]; then verdict=REJECT; why="elaboration failed"
  else
    axl="$(printf '%s\n' "$out" | tr '\n' ' ' | sed -n "s/.*'ArenaJudge.check' depends on axioms: \[\([^]]*\)\].*/\1/p" | tr ',' ' ')"
    if ! printf '%s\n' "$out" | grep -q "'ArenaJudge.check'"; then verdict=REJECT; why="no axiom report"; fi
    for a in $axl; do
      case " $allow " in *" $a "*) ;; *) verdict=REJECT; why="forbidden axiom $a";; esac
    done
  fi
  want=REJECT; case "$expect" in PASS*) want=PASS;; esac
  if [ "$verdict" = "$want" ]; then status=ok; else status=UNEXPECTED; fail=1; fi
  printf '%-28s %-7s %-10s (%s) expected: %s\n' "$name" "$verdict" "$status" "${why:-clean}" "$expect"
done
exit $fail
