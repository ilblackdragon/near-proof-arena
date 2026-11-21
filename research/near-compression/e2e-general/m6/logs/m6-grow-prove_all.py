#!/usr/bin/env python3
"""E2E M6 GROW: segprove the pre-checked segments containing memory.grow (MEMG rows) of every corpus
grow call (segcheck.jsonl), one call at a time; SEG_ONLY = those segments.

    prove_all.py SEGCHECK.jsonl OUT.jsonl [--limit N] [--all-segs]
"""
import json, os, re, subprocess, sys, time

D = '/data/illia/nearproof-deps/e2e-laneA/m6-grow'
BIN = '/data/illia/nearproof-deps/cargo-target-grow/release/nearproof-wasm-base'
SEGAIR = D + '/t1/airSegG.json'
src, out = sys.argv[1], sys.argv[2]
limit = int(sys.argv[sys.argv.index('--limit') + 1]) if '--limit' in sys.argv else None
allsegs = '--all-segs' in sys.argv
rows = [json.loads(l) for l in open(src)]
preps = {c['k']: c['prep'] for c in json.load(open(D + '/growcalls.json'))}
todo = []
for r in rows:
    segs = [s['i'] for s in r['segs'] if s['pre'] and (allsegs or s.get('grow', 0) + s.get('size', 0) > 0)]
    if segs:
        todo.append((r['steps'], r, segs))
todo.sort(key=lambda x: (x[0], x[1]['k']))
done = set()
if os.path.exists(out):
    for ln in open(out):
        done.add(json.loads(ln)['k'])
f = open(out, 'a')
n = 0
for steps, r, segs in todo:
    if r['k'] in done:
        continue
    if limit is not None and n >= limit:
        break
    n += 1
    t = time.time()
    # the lane-A prover lock is taken per call, so other sub-lanes' provers interleave
    p = subprocess.run(['flock', '/data/illia/nearproof-deps/e2e-laneA/prover.lock', BIN, 'segprove', SEGAIR, D + '/sweep/airs/' + r['air'], preps[r['k']], str(r['K'])],
                       capture_output=True, text=True,
                       env=dict(os.environ, SEG_CONTINUE='1', SEG_ONLY=','.join(map(str, segs)), RAYON_NUM_THREADS='8'))
    proofs = []
    for ln in p.stdout.splitlines():
        m = re.match(r'\s+PROOF (\d+): (\d+) B, prove ([\d.]+)s, verify (\d+) ms, statement ok.*peak_rss_kib (\d+)', ln)
        if m:
            proofs.append(dict(i=int(m[1]), bytes=int(m[2]), prove=float(m[3]), verify_ms=int(m[4]), rss_kib=int(m[5])))
    snd = re.search(r'SOUNDNESS total=([\d.]+)', p.stdout)
    row = dict(k=r['k'], steps=steps, K=r['K'], want=segs, proofs=proofs, bits=float(snd[1]) if snd else None,
               ok=len(proofs) == len(segs), rc=p.returncode, secs=round(time.time() - t, 1))
    if not row['ok']:
        row['err'] = p.stdout[-600:] + p.stderr[-800:]
    f.write(json.dumps(row) + '\n')
    f.flush()
    print(r['k'], steps, segs, [(q['bytes'], q['prove']) for q in proofs], row['ok'], flush=True)
