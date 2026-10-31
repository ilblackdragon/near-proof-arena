#!/bin/bash
# run.sh BIN TIER LIST OUT JOBS : one output file per batch (no interleaving), concatenated at the end
BIN=$1; T=$2; L=$3; O=$4; J=${5:-5}
TMP=$O.parts; rm -rf $TMP; mkdir -p $TMP
xargs -P $J -n 20 bash -c 'f=$(mktemp -p "$0" XXXXXX.jsonl); "$1" --tier "$2" "${@:3}" > "$f" 2>>"$0/err"' $TMP $BIN $T < $L
cat $TMP/*.jsonl > $O
cp $TMP/err $O.err 2>/dev/null
rm -rf $TMP
echo done >> $O.err
