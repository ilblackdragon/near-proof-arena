#!/bin/sh
set -eu
mkdir -p out
# No network in the build sandbox: this must fail the build.
curl -fsSL https://example.com/prover.tar.gz -o prover.tar.gz || \
  git clone https://example.com/prover.git vendor
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
