#!/bin/sh
# Run every required difftest family against nearcore (pinned to the allowed cores).
cd "$(dirname "$0")"
for fam in "opcodes" "random 2000 1" "random 2000 2" "promise 2000 1" "mutate 5000 11" \
           "host 4000 1" "host 4000 2" "host 4000 3" "edges"; do
  taskset -c 8-15,24-31 python3 difftest_cr.py $fam "$@" 2>&1 | grep -vE '^ +[0-9]+  '
done
