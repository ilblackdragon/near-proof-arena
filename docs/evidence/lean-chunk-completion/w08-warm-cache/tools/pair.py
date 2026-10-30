"""pair.py A.jsonl B.jsonl: cross-tab verdicts of two Lean result files (+ nearcore cold verdict and code label)."""
import collections, json, sys


def load(p):
    return {json.loads(l)['case']: json.loads(l) for l in open(p)}


a, b = load(sys.argv[1]), load(sys.argv[2])
c = collections.Counter()
ex = {}
for k in a:
    m = json.load(open(k + '/meta.json'))
    lab = ','.join(x for x in m.get('d3_violations') or [] if x.startswith('e.code')) or '-'
    key = (a[k]['verdict'], b[k]['verdict'], 'nearcore_' + ('ok' if m['nearcore'] == 'ok' else 'err'), lab,
           'same_reason' if a[k]['reason'] == b[k]['reason'] else 'reason_differs')
    c[key] += 1
    ex.setdefault(key, k)
for k, n in sorted(c.items(), key=lambda kv: -kv[1]):
    print(n, k, ex[k].split('/')[-3:])
