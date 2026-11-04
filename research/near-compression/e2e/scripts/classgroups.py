"""D-7 (review-D6 F1): which scanned D0a chunks can share a base shape class?
A group can share class logs L = max of its members' compact logs iff every member can be re-cut at L:
L_t <= the member's classical render log for every table t whose compact log is below L_t (a re-cut
cannot grow past the classical render; measured: walk, acct fail). Prints the largest groups found
greedily, and the pairs including the D-6 chunks."""
import json, pathlib, sys, itertools
root = pathlib.Path(sys.argv[1])
H = {}
for d in sorted(root.iterdir()):
    f = d / 'heights.json'
    if f.exists():
        H[d.name] = json.loads(f.read_text())
names = sorted(H)
tables = list(H[names[0]].keys())
def ok(group):
    L = {t: max(H[c][t]['log'] for c in group) for t in tables}
    for c in group:
        for t in tables:
            if L[t] > H[c][t]['log'] and L[t] > H[c][t]['classical_log']:
                return None
    return L
print('chunks', len(names))
# greedy: seed with each chunk, add chunks keeping feasibility, prefer the smallest cell growth
best = []
for s in names:
    g = [s]
    for c in names:
        if c != s and ok(g + [c]) is not None:
            g.append(c)
    best.append(g)
best.sort(key=len, reverse=True)
seen = set()
for g in best[:8]:
    k = tuple(sorted(g))
    if k in seen: continue
    seen.add(k)
    print(len(g), g)
for a in ['00-h10006-s3', '00-h10007-s0']:
    mates = [c for c in names if c != a and ok([a, c]) is not None]
    print('pair-mates of', a, len(mates), mates)
