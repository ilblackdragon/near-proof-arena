"""Run nearspec-v3-check-successor over a case list for several tiers in parallel.

usage: census.py BIN CASELIST OUTDIR TIER[,TIER...] [JOBS] [BATCH]
Appends checker rows to OUTDIR/<tier>.jsonl as batches finish (resumable: cases already present
are skipped). Rows are the checker's own {"case","tier","verdict","reason"} lines.
"""
import json, os, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

bin_, caselist, outdir, tiers = sys.argv[1:5]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 30
batch = int(sys.argv[6]) if len(sys.argv) > 6 else 200
cases = [l.strip() for l in open(caselist) if l.strip()]
os.makedirs(outdir, exist_ok=True)


def run(tier, chunk, f, lock):
    p = subprocess.run([bin_, '--tier', tier] + chunk, capture_output=True, text=True)
    rows = [l for l in p.stdout.splitlines() if l.startswith('{')]
    if len(rows) != len(chunk):
        raise RuntimeError(f'{tier}: got {len(rows)} rows for {len(chunk)} cases rc={p.returncode} {p.stderr[:500]}')
    with lock:
        f.write('\n'.join(rows) + '\n')
        f.flush()


for tier in tiers.split(','):
    t0 = time.time()
    path = os.path.join(outdir, tier + '.jsonl')
    done = set()
    if os.path.exists(path):
        for l in open(path):
            try:
                done.add(json.loads(l)['case'])
            except Exception:
                pass
    todo = [c for c in cases if c not in done]
    chunks = [todo[i:i + batch] for i in range(0, len(todo), batch)]
    lock = threading.Lock()
    with open(path, 'a') as f, ThreadPoolExecutor(jobs) as ex:
        list(ex.map(lambda c: run(tier, c, f, lock), chunks))
    print(tier, len(cases), f'{time.time() - t0:.1f}s', flush=True)
