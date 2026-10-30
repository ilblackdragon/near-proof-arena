"""beforeafter.py BEFORE.jsonl AFTER.jsonl: completeCodeGlobal verdict transitions with the nearcore cold label."""
import collections, json, sys


def load(p):
    return {json.loads(l)['case']: json.loads(l) for l in open(p)}


b, a = load(sys.argv[1]), load(sys.argv[2])
c = collections.Counter()
for k in a:
    if k not in b:
        continue
    m = json.load(open(k + '/meta.json'))
    nc = 'ok' if m.get('nearcore') == 'ok' else 'err'
    same = 'same_reason' if a[k]['reason'] == b[k]['reason'] else 'reason_changed'
    ra = a[k]['reason'][:45] if a[k]['verdict'] != 'accept' else ''
    c[(b[k]['verdict'], a[k]['verdict'], 'nearcore_' + nc, same, ra)] += 1
print('cases', sum(c.values()))
for k, n in sorted(c.items(), key=lambda kv: -kv[1]):
    print(n, k)
bad = sum(n for k, n in c.items() if k[1] == 'accept' and k[2] == 'nearcore_err')
print('Lean accept of nearcore reject:', bad)
