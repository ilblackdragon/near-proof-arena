#!/usr/bin/env python3
"""table.py OUTJSON LABEL=FILE.jsonl ... : verdict vs nearcore per replay file.

A row is: case, tier verdict, nearcore ('ok'/'err'). Classification:
  agree        accept & ok, or reject & err
  ood          out of domain (never compared, never an accept)
  UNSOUND      accept & err   (a Lean accept of a nearcore reject)
  valid-reject reject & ok
Race arm = reason contains 'pipelined before the in-chunk deploy'."""
import collections, json, sys
res = {}
for arg in sys.argv[2:]:
    label, path = arg.split('=', 1)
    c = collections.Counter(); race = collections.Counter(); seeds = set(); examples = {}
    for line in open(path):
        r = json.loads(line)
        meta = json.load(open(r['case'] + '/meta.json'))
        nc = 'ok' if meta['nearcore'] == 'ok' else 'err'
        v = r['verdict']
        cls = ('ood' if v == 'out_of_domain' else
               'agree' if (v == 'accept') == (nc == 'ok') else
               'UNSOUND' if v == 'accept' else 'valid-reject')
        c[cls] += 1
        seeds.add(r['case'].split('/')[-3])
        if 'pipelined before the in-chunk deploy' in r['reason']:
            race[nc] += 1
            examples.setdefault('race', r['case'])
        if cls in ('UNSOUND', 'valid-reject'):
            examples.setdefault(cls, []).append((r['case'], r['reason'][:160]))
    res[label] = {'cases': sum(c.values()), 'runs': sorted(seeds), **dict(c),
                  'race_arm_by_nearcore': dict(race), 'examples': examples}
json.dump(res, open(sys.argv[1], 'w'), indent=1)
for k, v in res.items():
    print(k, {x: v[x] for x in v if x != 'examples'})
