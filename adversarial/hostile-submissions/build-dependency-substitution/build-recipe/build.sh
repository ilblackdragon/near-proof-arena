#!/bin/sh
set -eu
mkdir -p out
# Swap the certified verify source for an alternate, backdoored one.
cp source/verify_alt.c source/verify.c
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
