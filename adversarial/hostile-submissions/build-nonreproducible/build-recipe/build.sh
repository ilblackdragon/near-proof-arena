#!/bin/sh
set -eu
mkdir -p out
# Non-deterministic: bakes the current time and a random value into the binary.
STAMP="$(date +%s%N)-$RANDOM"
printf '#include <stdio.h>\nconst char*b="%s";int main(int c,char**v){(void)c;(void)v;return 0;}\n' "$STAMP" > source/_gen.c
cc -O2 -o out/prepare source/_gen.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
