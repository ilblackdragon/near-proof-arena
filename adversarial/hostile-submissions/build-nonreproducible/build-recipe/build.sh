#!/bin/sh
set -eu
mkdir -p out
# Non-deterministic: bake random bytes into the verifier.
R="$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \n')"
printf 'const char *build_nonce = "%s";\n' "$R" > source/_nonce.c
cc -O2 -std=c99 -o out/prepare source/common.c source/prepare.c
cc -O2 -std=c99 -o out/prove   source/common.c source/prove.c
cc -O2 -std=c99 -o out/verify  source/common.c source/verify.c source/_nonce.c
