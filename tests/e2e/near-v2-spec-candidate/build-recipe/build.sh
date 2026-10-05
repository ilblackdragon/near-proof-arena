#!/bin/sh
# Offline, reproducible: plain cc; bin/nearspec-check is supplied by the test.
set -eu
mkdir -p out
for t in prepare prove verify; do
  cc -O2 -std=c99 -Wall -o "out/$t" source/common.c "source/$t.c"
done
cp bin/nearspec-check out/nearspec-check
chmod 0755 out/nearspec-check
