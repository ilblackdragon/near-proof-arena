#!/usr/bin/env python3
"""Per-chunk digest equality between a run without and with producer memtries (same seed):
compare_memtries.py runs/s1.json runs/s1-mem.json"""
import json, sys
a = json.load(open(sys.argv[1]))["chunks"]; b = json.load(open(sys.argv[2]))["chunks"]
strip = lambda c: {k: v for k, v in c.items() if k != "producer_memtrie"}
same = sum(strip(x) == strip(y) for x, y in zip(a, b))
print(f"chunks {len(a)}/{len(b)} identical {same} outcomes {sum(len(c['outcomes']) for c in a)}")
sys.exit(0 if len(a) == len(b) == same else 1)
