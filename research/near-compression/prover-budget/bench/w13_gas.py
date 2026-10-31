#!/usr/bin/env python3
"""Gas distribution of the shard-13 mainnet replay cases, from tools/d3/claim_outputs.py output.

    for d in /data/illia/nearproof-deps/mainnet-w13/replay-cases/*/; do
      python3 tools/d3/claim_outputs.py "$d/claim.bin"; done > w13.jsonl
    python3 w13_gas.py w13.jsonl

`gasBurnt` is the endorsed chunk header's gas field as decoded by claim_outputs.py.
Quantile = sorted[int(p * n)] (no interpolation).
"""
import json
import sys

g = sorted(json.loads(line)["outputs"]["gasBurnt"] for line in open(sys.argv[1]))
n = len(g)


def q(p):
    return g[min(n - 1, int(p * n))]


print(json.dumps({
    "chunks": n,
    "zero_gas_chunks": sum(1 for x in g if x == 0),
    "mean_tgas": round(sum(g) / n / 1e12, 2),
    "p50_tgas": round(q(0.5) / 1e12, 2),
    "p90_tgas": round(q(0.9) / 1e12, 2),
    "p99_tgas": round(q(0.99) / 1e12, 2),
    "p99.9_tgas": round(q(0.999) / 1e12, 2),
    "max_tgas": round(g[-1] / 1e12, 2),
}, indent=1))
