#!/usr/bin/env bash
# Collect one run into results/ and copy its small logs into logs/<name>/. usage: archive_run.sh RUN_DIR
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
R=${1:?run}
N=$(basename "$R")
python3 "$HERE/collect.py" "$R" "$HERE/../results"
mkdir -p "$HERE/../logs/$N"
for f in base.log chain.log verify.log negatives.log STAGES.txt RESULT.json NEGATIVES.json RUN.json validate-base.log dump.log public.log; do
  [ -f "$R/$f" ] && cp "$R/$f" "$HERE/../logs/$N/"
done
du -sh "$HERE/../logs/$N"
