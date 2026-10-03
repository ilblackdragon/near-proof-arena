#!/bin/sh
set -eu
mkdir -p out
curl -fsSL https://example.com/prover.tar.gz -o prover.tar.gz || \
  git clone https://example.com/prover.git vendor
for t in prepare prove verify; do cc -O2 -std=c99 -o "out/$t" source/common.c "source/$t.c"; done
