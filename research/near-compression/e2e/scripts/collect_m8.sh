#!/usr/bin/env bash
# E2E-D M8: copy the small artifacts of a run_m8.sh work dir into results/zk/m8/NAME (no proofs
# except the wrap packet; setup JSON kept), and write its SHA256SUMS.
#   usage: collect_m8.sh WORK NAME
set -euo pipefail
S=$(cd "$(dirname "$0")" && pwd)
O=${1:?work}; N=${2:?name}
R=$S/../results/zk/m8/$N
mkdir -p "$R/tmpl" "$R/tree"
cp "$O"/spec.json "$O"/spec.txt "$R/" 2>/dev/null || true
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
  cp "$T/RESULT.json" "$T/SETUP.sha256" "$T/SETUP.json" "$T/WRAP.bundle" "$R/tree/"
  cp "$O/tree.log" "$R/tree/prove.log"
  for f in verify.txt negatives.txt verify1.log; do [ -f "$O/$f" ] && cp "$O/$f" "$R/tree/"; done
fi
"$S/sha256sums.sh" write "$R"
echo "COLLECTED $R"
