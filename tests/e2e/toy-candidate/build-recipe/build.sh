#!/bin/sh
# Offline, reproducible: plain cc, no timestamps embedded.
set -eu
mkdir -p out
for t in prepare prove verify; do
  cc -O2 -std=c99 -Wall -o "out/$t" source/common.c "source/$t.c"
done
