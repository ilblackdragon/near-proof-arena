#!/usr/bin/env bash
# E2E-D M9: copy the small artifacts of a run_m9.sh work dir into results/zk/m9/NAME (no proofs
# except the wrap packet; setup JSON kept), and write its SHA256SUMS.
#   usage: collect_m9.sh WORK NAME
set -euo pipefail
S=$(cd "$(dirname "$0")" && pwd)
O=${1:?work}; N=${2:?name}
R=$S/../results/zk/m9/$N
mkdir -p "$R/tmpl" "$R/tree"
for f in spec.json spec.txt imported.sha256 programs.log; do [ -f "$O/$f" ] && cp "$O/$f" "$R/"; done
for d in "$O"/tmpl/*/; do
  t=$(basename "$d"); mkdir -p "$R/tmpl/$t"
  cp "$d/INFO.json" "$R/tmpl/$t/"
  sha256sum "$d/TMPL.vk.json" "$d/TMPL.proof" | sed "s#$d##" > "$R/tmpl/$t/files.sha256"
done
cp "$O"/tmpl-*.log "$R/tmpl/" 2>/dev/null || true
[ -f "$O/laneA/segcheck.log" ] && cp "$O/laneA/segcheck.log" "$O/laneA/inputs.sha256" "$R/tmpl/" || true
[ -f "$O/laneB/gen.txt" ] && cp "$O/laneB/gen.txt" "$R/tmpl/laneB-gen.txt" || true
T=$O/tree
if [ -d "$T" ]; then
  for f in RESULT.json SETUP.sha256 SETUP.json WRAP.bundle; do [ -f "$T/$f" ] && cp "$T/$f" "$R/tree/"; done
  cp "$O/tree.log" "$R/tree/prove.log"
  for f in verify.txt negatives.txt negatives9.txt verify1.log swap.log; do [ -f "$O/$f" ] && cp "$O/$f" "$R/tree/"; done
fi
"$S/sha256sums.sh" write "$R"
echo "COLLECTED $R"
