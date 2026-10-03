#!/bin/sh
# Offline build: no network, cc + /bin/sh assumed present in the build image.
set -eu
mkdir -p out
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
