#!/bin/bash
# pfvm.sh <out-dir> <public-dir> <cases-dir> <rounds> [K=V env exported in the guest...]
# One Firecracker VM (arena launch path, 8 vCPUs on host CPUs 8-15, 16 GiB):
# for each round, each case: time `prove` (guest wall incl. process start).
out=$1 pub=$2 cases=$3 rounds=$4; shift 4
ex=""; for e in "$@"; do ex="$ex export $e;"; done
script="$ex"'for r in $(seq '$rounds'); do for c in $(ls /in/c | grep "^s"); do t0=$(date +%s%N); /in/b/prove --public /in/p --request /in/c/$c/request.bin --witness /in/c/$c/witness.bin --claim-out /scratch/c.bin --proof-out /scratch/p.bin 2>/scratch/err; rc=$?; t1=$(date +%s%N); cmp -s /scratch/c.bin /in/c/$c/expected_claim.bin && ok=ok || ok=BAD; echo "r$r $c rc=$rc $ok $(( (t1-t0)/1000000 ))ms"; [ $r = '$rounds' ] && grep "^\[prove\]" /scratch/err | grep -v "^\[prove\]   " | tr "\n" " " && echo; done; done'
HEAVY_MEM=24G /data/illia/nearproof-deps/bin/heavy /data/illia/nearproof/target/debug/arena-fc-run --cpus 8,9,10,11,12,13,14,15 --mem-mb 16384 --scratch-mb 2048 --timeout-s 3000 --ro $out:/in/b --ro $pub:/in/p --ro $cases:/in/c -- /bin/bash -c "$script" | python3 -c "import json,sys; d=json.load(sys.stdin); print(d['stdout_trunc']); print(d['stderr_trunc'][-300:]); print(d['exit'])"
