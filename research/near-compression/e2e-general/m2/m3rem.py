import json, collections, sys


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


m3 = load(sys.argv[1])
cases = {c for c, _ in m3}
m2 = load('/data/illia/nearproof-deps/e2e-laneA/m2/rows.jsonl', cases)
c = collections.Counter()
why = collections.Counter()
trans = collections.Counter()
ex = {}
for key, r2 in m2.items():
    r3 = m3.get(key)
    trans[(r2['class'], r3['class'] if r3 else None)] += 1
    if r2['class'] in ('unchipped', 'trace-failed') and r3:
        c[r3['class']] += 1
        if r3['class'] not in ('equal', 'equal-abort'):
            t = r3.get('trace') or {}
            w = str(r3.get('why') or t.get('err') or '')[:140]
            why[(r3['class'], w)] += 1
            ex.setdefault((r3['class'], w), r3.get('prep'))
print('remainder ->', sum(c.values()), dict(c))
for k, v in why.most_common():
    print(v, k, ex[k])
print('transitions', dict(trans))
br = collections.Counter()
for key, r2 in m2.items():
    r3 = m3.get(key)
    if r2['class'] == 'unchipped' and r3:
        w2 = str((r2.get('trace') or {}).get('err') or '')[:60]
        w3 = str((r3.get('trace') or {}).get('err') or '')[:70] if r3['class'] == 'trace-failed' else ''
        br[(w2, r3['class'], w3)] += 1
for k, v in br.most_common():
    print(v, k)
