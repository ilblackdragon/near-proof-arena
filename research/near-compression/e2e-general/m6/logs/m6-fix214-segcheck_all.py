#!/usr/bin/env python3
"""E2E M6 GROW: segcheck every corpus call that executes memory.grow, at wasmBaseSegAirG.

    segcheck_all.py OUT.jsonl [--only N]
K = clamp(2^ceil(log2(steps/4)), 64, 2^18): about 4 segments per call (up to 6 for the 1.4M-step calls).
"""
import json, math, os, re, subprocess, sys, time

D = '/data/illia/nearproof-deps/e2e-laneA/m6-grow'
BIN = '/data/illia/nearproof-deps/e2e-laneA/m6-fix214/nearproof-wasm-base'
SEGAIR = '/data/illia/nearproof-deps/e2e-laneA/m6-fix214/airSegG.json'
out = sys.argv[1]
calls = [c for c in json.load(open(D + '/growcalls.json')) if c['cls'].startswith('equal')]
calls.sort(key=lambda c: c['k'])
if '--only' in sys.argv:
    calls = calls[:int(sys.argv[sys.argv.index('--only') + 1])]
done = set()
if os.path.exists(out):
    for ln in open(out):
        done.add(json.loads(ln)['k'])
f = open(out, 'a')
for c in calls:
    if c['k'] in done:
        continue
    p = json.load(open(c['prep']))
    air = D + '/sweep/airs/air-%d-%d.json' % (len(p['localTags']), p['ngl'])
    K = min(max(2 ** math.ceil(math.log2(max(c['steps'] / 4, 1))), 64), 2 ** 18)
    t = time.time()
    r = subprocess.run([BIN, 'segcheck', SEGAIR, air, c['prep'], str(K)], capture_output=True, text=True,
                       env=dict(os.environ, SEG_CONTINUE='1', RAYON_NUM_THREADS='8'))
    dt = time.time() - t
    segs = []
    cur = None
    buildfail = None
    for ln in r.stdout.splitlines():
        m = re.match(r'SEG (\d+) t \((\d+), (\d+)\] steps (\d+) halted (\d+)', ln)
        if m:
            cur = dict(i=int(m[1]), t0=int(m[2]), t1=int(m[3]), halted=int(m[5]), pre=False)
            segs.append(cur)
        elif ln.startswith('  GROW') and cur is not None:
            m = re.search(r'pages (\d+) -> (\d+) \| grown blocks \(MEMBG\) (\d+) \| old blocks above 64 MiB \(MEMBH\) (\d+) \| depth lift (\w+)', ln)
            cur.update(pages=[int(m[1]), int(m[2])], membg=int(m[3]), membh=int(m[4]), lift=m[5] == 'true')
        elif ln.startswith('  MEMG rows') and cur is not None:
            m = re.search(r'memory.grow (\d+) \(succeeded (\d+), failed (\d+)\) memory.size (\d+)', ln)
            cur.update(grow=int(m[1]), grow_ok=int(m[2]), grow_fail=int(m[3]), size=int(m[4]))
        elif ln.startswith('  PRECHECK OK') and cur is not None:
            cur['pre'] = True
        elif ln.startswith('  PRECHECK FAIL') and cur is not None:
            cur['fail'] = ln[17:300]
        elif ln.startswith('SEGBUILD FAIL'):
            buildfail = ln[:300]
    row = dict(k=c['k'], case=c['case'], cls=c['cls'], steps=c['steps'], K=K, air=os.path.basename(air),
               ok='SEGCHECK OK' in r.stdout, rc=r.returncode, buildfail=buildfail,
               nseg=math.ceil(c['steps'] / K), secs=round(dt, 2), segs=segs)
    if not row['ok']:
        row['err'] = (r.stdout[-400:] + r.stderr[-800:])
    f.write(json.dumps(row) + '\n')
    f.flush()
    print(c['k'], c['steps'], K, len(segs), row['ok'], round(dt, 1), flush=True)
