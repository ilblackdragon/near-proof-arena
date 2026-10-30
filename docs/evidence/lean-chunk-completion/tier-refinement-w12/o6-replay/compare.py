"""Compare two tiers' per-case verdicts: VRefines lo hi (accept->accept, reject->reject)."""
import collections, json, sys


def load(p):
    d = {}
    for line in open(p):
        r = json.loads(line)
        d[r.get('case') or r.get('case_dir')] = r
    return d


lo, hi = load(sys.argv[1]), load(sys.argv[2])
assert set(lo) == set(hi), (len(lo), len(hi))
table = collections.Counter()
viol = []
reason_only = 0
for k in sorted(lo):
    a, b = lo[k], hi[k]
    table[(a['verdict'], b['verdict'])] += 1
    if a['verdict'] in ('accept', 'reject') and a['verdict'] != b['verdict']:
        viol.append((k, a['verdict'], a.get('reason'), b['verdict'], b.get('reason')))
    elif a['verdict'] == 'reject' and a.get('reason') != b.get('reason'):
        reason_only += 1
        print('REASON', k, a.get('reason'), '|', b.get('reason'))
for v in viol:
    print('VIOLATION', *v)
print(json.dumps({'cases': len(lo), 'pairs': {f'{x}->{y}': n for (x, y), n in sorted(table.items())},
                  'violations': len(viol), 'reject_reason_differs': reason_only}))
