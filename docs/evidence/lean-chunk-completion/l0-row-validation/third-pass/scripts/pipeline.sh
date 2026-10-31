#!/bin/bash
# pass 1 (both variants) -> honest list -> --blind outputs of the pre-fix checker -> pass 2 (cont)
set -u
cd /data/illia/nearproof-deps/l0-validate/b4/gk
rm -f overrides-*.json
PASS=1 bash gen.sh
python3 honest.py p1 | tail -1
python3 blind.py /data/illia/nearproof-deps/gateb-freeze-2368b8713/checker allFeatures before-allFeatures
python3 blind.py /data/illia/nearproof-deps/gateb-freeze-2368b8713/checker signed before-signed
PASS=2 VARIANTS=cont bash gen.sh
for s in 31 32 33 34; do diff -rq p1-cont-$s/ood p2-cont-$s/ood > /dev/null && echo "ood same $s" || echo "ood DIFF $s"; done
ls -d p2-cont-*/mutants/*lean_outputs | wc -l
