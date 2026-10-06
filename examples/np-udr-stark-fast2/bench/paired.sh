#!/bin/bash
# paired.sh <class r1|r16|r256> <rounds>: alternate parent / fast2 batches (8 requests, one VM each)
B=/data/illia/nearproof-wt/zk-L8f-bench
P=/data/illia/nearproof-wt/zk-L8d/examples/np-udr-stark/out
F=/data/illia/nearproof-wt/zk-L8f/examples/np-udr-stark-fast2/out
for r in $(seq $2); do
  for pair in "parent:$P" "fast2:$F"; do
    tag=${pair%%:*}; o=${pair#*:}
    res=$($B/pfvm.sh $o $B/parent/public $B/cases8/$1/cases 1)
    bad=$(echo "$res" | grep -c "BAD\|rc=[1-9]")
    tot=$(echo "$res" | grep -o "[0-9]*ms" | tr -d ms | paste -sd+ | bc)
    echo "$1 round $r $tag batch ${tot}ms bad=$bad"
  done
done
