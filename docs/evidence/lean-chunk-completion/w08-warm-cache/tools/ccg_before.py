"""Characterise the completeCodeGlobal w.code_complete rejects of the pre-change binary (STRAT)."""
import collections, json, sys
rows = [json.loads(l) for l in open(sys.argv[1])]
c = collections.Counter()
ex = {}
for r in rows:
    if 'w.code_complete' not in r['reason']:
        continue
    m = json.load(open(r['case'] + '/meta.json'))
    fam = r['case'].split('/corpora/')[1].split('/')[0] + '/' + r['case'].split('/')[-2]
    k = (fam, m.get('nearcore') == 'ok', tuple(x for x in (m.get('d3_violations') or []) if x.startswith('e.code')))
    c[k] += 1
    ex.setdefault(k, r['case'])
for k, n in sorted(c.items(), key=lambda kv: -kv[1]):
    print(n, k, ex[k].split('/corpora/')[1])
