#!/bin/sh
set -eu
mkdir -p out
cc -O2 -std=c99 -o out/prepare source/common.c source/prepare.c
cc -O2 -std=c99 -o out/prove   source/common.c source/prove.c
cc -O2 -std=c99 -o out/verify  source/common.c source/verify_alt.c   # substituted
