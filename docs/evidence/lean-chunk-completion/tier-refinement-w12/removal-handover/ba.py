"""Before/after verdict diff with nearcore labels.
usage: ba.py NAME BEFORE.jsonl[.gz] AFTER.jsonl[.gz]
Prints the transition counts, moves toward/away from nearcore, Lean accepts of nearcore rejects (after),
and reject->ood moves."""
import json, sys, gzip, collections


def rows(p):
    f = gzip.open(p, 'rt') if p.endswith('.gz') else open(p)
    return {json.loads(l)['case']: json.loads(l) for l in f}


name, bp, ap = sys.argv[1:4]
b, a = rows(bp), rows(ap)
assert set(b) == set(a), (len(b), len(a), len(set(b) ^ set(a)))
meta = {}
c = collections.Counter()
moves = collections.Counter()
reasons = collections.Counter()
for k in a:
    vb, va = b[k]['verdict'], a[k]['verdict']
    if k not in meta:
        try:
            meta[k] = json.load(open(f'{k}/meta.json'))['expected_rel']
        except Exception:
            meta[k] = None
    exp = meta[k]
    c[f'after:{va}'] += 1
    if va == 'accept' and exp is False:
        c['UNSOUND_after'] += 1
    if (vb, b[k].get('reason')) != (va, a[k].get('reason')):
        tag = f'{vb}->{va}'
        if vb == va:
            tag += ' (reason)'
        toward = (exp is True and va == 'accept') or (exp is False and va == 'reject')
        away = (exp is True and vb == 'accept') or (exp is False and vb == 'reject')
        moves[(tag, 'nearcore ok' if exp else 'nearcore reject' if exp is False else '?',
               'toward' if toward and not away else 'away' if away and not toward else 'neutral')] += 1
        reasons[(b[k].get('reason', '')[:50], a[k].get('reason', '')[:50])] += 1
out = {'name': name, 'cases': len(a), 'counts': dict(c), 'moves': {' | '.join(k): v for k, v in moves.items()},
       'reason_pairs': {f'{x} => {y}': n for (x, y), n in reasons.most_common(12)}}
print(json.dumps(out, indent=1, ensure_ascii=False))
