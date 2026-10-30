#!/usr/bin/env python3
"""diff.py BEFORE.jsonl AFTER.jsonl : verdict counts before/after and every changed case."""
import collections, json, sys
def load(p):
    return {json.loads(l)['case']: json.loads(l) for l in open(p)}
b, a = load(sys.argv[1]), load(sys.argv[2])
assert b.keys() == a.keys(), 'populations differ'
cb = collections.Counter(r['verdict'] for r in b.values())
ca = collections.Counter(r['verdict'] for r in a.values())
changed = [(k, b[k]['verdict'], a[k]['verdict'], a[k]['reason'][:120]) for k in sorted(b)
           if (b[k]['verdict'], b[k]['reason']) != (a[k]['verdict'], a[k]['reason'])]
print(json.dumps({'cases': len(b), 'before': cb, 'after': ca, 'changed': len(changed),
                  'transitions': collections.Counter((x[1], x[2]) for x in changed).most_common(),
                  'examples': changed[:20]}, indent=1, default=str))
