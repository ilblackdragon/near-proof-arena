import json, sys, collections


def load(p):
    out = {}
    for l in open(p):
        r = json.loads(l)
        out[r.get('case') or r.get('case_dir')] = r
    return out


lo = load(sys.argv[1])
hi = load(sys.argv[2])
assert set(lo) == set(hi)
c = collections.Counter()
viol = []
for k in lo:
    a, b = lo[k], hi[k]
    c[(a['verdict'], b['verdict'])] += 1
    if a['verdict'] != 'out_of_domain' and (a['verdict'], a.get('reason')) != (b['verdict'], b.get('reason')):
        viol.append((k, a['verdict'], a.get('reason'), b['verdict'], b.get('reason')))
print(json.dumps({'cases': len(lo), 'pairs': {f'{x}->{y}': n for (x, y), n in sorted(c.items())},
                  'violations': len(viol)}))
for v in viol:
    print('VIOL', *v)
