"""Round 3 (2026-10-31): compare checker rows before (main, guarded vmCall) and after (guard
removed). Usage: compare-r3.py rows-before.jsonl[.gz] rows-after.jsonl[.gz]"""
import collections, gzip, json, sys


def load(f):
    op = gzip.open if f.endswith('.gz') else open
    d = {}
    with op(f, 'rt') as fh:
        for l in fh:
            l = l.strip()
            if l.startswith('{'):
                r = json.loads(l)
                d[r.get('case') or r.get('dir')] = r
    return d


def pop(c):
    p = c.split('/corpora/')
    return p[1].split('/')[0] if len(p) > 1 else 'fixtures'


b, a = load(sys.argv[1]), load(sys.argv[2])
tab = collections.defaultdict(collections.Counter)
moved = []
for c in sorted(set(a) | set(b)):
    rb, ra = b.get(c), a.get(c)
    t = tab[pop(c)]
    t['cases'] += 1
    if rb is None or ra is None:
        t['missing'] += 1
        moved.append(c)
        continue
    for side, r in (('before', rb), ('after', ra)):
        t[f"{side}_{r.get('verdict')}"] += 1
    if (rb.get('verdict'), rb.get('reason')) != (ra.get('verdict'), ra.get('reason')):
        t['moved'] += 1
        moved.append(c)
    if 'fuel_certificate' in str(rb.get('reason')):
        t['before_fuel_certificate'] += 1
print('| population | cases | accept (before → after) | reject | out of domain | `w.fuel_certificate` before | moved |')
print('|---|---|---|---|---|---|---|')
tot = collections.Counter()
for p in sorted(tab):
    t = tab[p]
    tot.update(t)
    f = lambda k: f"{t['before_' + k]:,} → {t['after_' + k]:,}"
    print(f"| {p} | {t['cases']:,} | {f('accept')} | {f('reject')} | {f('out_of_domain')} | "
          f"{t['before_fuel_certificate']} | {t['moved'] + t['missing']} |")
print(f"| **total** | **{tot['cases']:,}** | | | | {tot['before_fuel_certificate']} | **{tot['moved'] + tot['missing']}** |")
other = {k: v for k, v in tot.items() if k.split('_', 1)[-1] not in ('accept', 'reject', 'out_of_domain')
         and k not in ('cases', 'moved', 'missing', 'before_fuel_certificate')}
if other:
    print('other verdicts:', other)
print('moved/missing:', len(moved), moved[:10])
