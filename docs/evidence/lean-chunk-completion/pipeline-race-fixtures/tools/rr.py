#!/usr/bin/env python3
"""Ad-hoc replay: rr.py BINARY TIER CASELIST OUT.jsonl [jobs] — runs the checker in batches of 25."""
import json, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
binary, tier, lst, out = sys.argv[1:5]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 4
cases = [l.strip() for l in open(lst) if l.strip()]
batches = [cases[i:i + 25] for i in range(0, len(cases), 25)]
def run(b):
    r = subprocess.run([binary, '--tier', tier, *b], capture_output=True, text=True, timeout=7200)
    rows = [json.loads(l) for l in r.stdout.splitlines() if l.strip()]
    if len(rows) != len(b):
        raise SystemExit(f'batch failed: {r.returncode} {r.stderr[:500]}')
    return rows
with ThreadPoolExecutor(jobs) as ex, open(out, 'w') as f:
    for rows in ex.map(run, batches):
        for row in rows:
            f.write(json.dumps(row) + '\n')
print(len(cases))
