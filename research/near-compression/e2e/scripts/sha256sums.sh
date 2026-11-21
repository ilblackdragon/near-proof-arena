#!/usr/bin/env bash
# SHA256SUMS of a results directory: every regular file below DIR (recursive, paths relative to DIR,
# byte-sorted), except files named SHA256SUMS (the manifest itself and any nested one).
# usage: sha256sums.sh write DIR...   -> DIR/SHA256SUMS
#        sha256sums.sh check DIR...   exit 1 on a mismatch, a missing file, or a file not listed
set -euo pipefail
export LC_ALL=C
files() { (cd "$1" && find . -type f ! -name SHA256SUMS -printf '%P\0' | sort -z); }
mode=${1:?usage: sha256sums.sh write|check DIR...}; shift
[ $# -gt 0 ] || { echo "usage: sha256sums.sh write|check DIR..." >&2; exit 2; }
bad=0
for d in "$@"; do
  [ -d "$d" ] || { echo "SHA256SUMS: not a directory: $d" >&2; exit 2; }
  case $mode in
  write)
    sums=$(files "$d" | (cd "$d" && xargs -0 -r sha256sum --))
    if [ -n "$sums" ]; then printf '%s\n' "$sums" > "$d/SHA256SUMS"; else : > "$d/SHA256SUMS"; fi
    echo "SHA256SUMS_WRITTEN $d/SHA256SUMS ($(wc -l < "$d/SHA256SUMS") files)"
    ;;
  check)
    if [ ! -f "$d/SHA256SUMS" ]; then echo "SHA256SUMS_MISSING $d"; bad=1; continue; fi
    ok=1
    if [ -s "$d/SHA256SUMS" ]; then
      (cd "$d" && sha256sum --quiet --strict -c SHA256SUMS) || ok=0
    fi
    unlisted=$(comm -23 <(files "$d" | tr '\0' '\n') <(cut -c67- "$d/SHA256SUMS" | sort))
    if [ -n "$unlisted" ]; then ok=0; while IFS= read -r f; do echo "SHA256SUMS_UNLISTED $d/$f"; done <<< "$unlisted"; fi
    if [ $ok = 1 ]; then echo "SHA256SUMS_OK $d ($(wc -l < "$d/SHA256SUMS") files)"; else echo "SHA256SUMS_FAILED $d"; bad=1; fi
    ;;
  *) echo "usage: sha256sums.sh write|check DIR..." >&2; exit 2 ;;
  esac
done
exit $bad
