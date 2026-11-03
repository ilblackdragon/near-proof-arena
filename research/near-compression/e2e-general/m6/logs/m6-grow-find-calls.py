import json, collections


def load(path, cases=None):
    per = collections.defaultdict(list)
    for ln in open(path):
        r = json.loads(ln)
        if cases is None or r['case'] in cases:
            per[r['case']].append(r)
    out = {}
    for c, rs in per.items():
        rs.sort(key=lambda r: r['k'])
        for i, r in enumerate(rs):
            out[(c, i)] = r
    return out


m3 = load('/data/illia/nearproof-deps/e2e-laneA/m6-grow/sweep/rows.jsonl')
cases = {c for c, _ in m3}
m2 = load('/data/illia/nearproof-deps/e2e-laneA/m2/rows.jsonl', cases)
g = []
c = collections.Counter()
for key, r2 in m2.items():
    e = str((r2.get('trace') or {}).get('err') or r2.get('why') or '')
    if '0x240' in e:
        r3 = m3.get(key)
        assert r3 and r3['method'] == r2['method']
        c[r3['class']] += 1
        g.append(r3)
print(len(g), c)
st = sorted((r.get('trace') or {}).get('steps') or 0 for r in g if r['class'].startswith('equal'))
print(len(st), st[:5], st[len(st) // 2], st[-5:], sum(st))
for r in g:
    if r['class'] == 'trace-failed':
        print(r['err'][:120])
json.dump([dict(case=r['case'], k=r['k'], prep=r.get('prep'), cls=r['class'],
                steps=(r.get('trace') or {}).get('steps'), method=r['method']) for r in g],
          open('/data/illia/nearproof-deps/e2e-laneA/m6-grow/growcalls.json', 'w'), indent=0)
