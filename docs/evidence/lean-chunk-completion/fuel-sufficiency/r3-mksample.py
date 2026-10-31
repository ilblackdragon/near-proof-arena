"""1-in-8 seeded sample of every corpus population (all of the small ones), plus the fixture
cases of the round-2 guard sample. Output: one case directory per line."""
import os, random, sys

root = '/data/illia/nearproof-deps/corpora'
prev = '/data/illia/nearproof/.claude/worktrees/agent-ad85d3164f60ab14a/docs/evidence/lean-chunk-completion/fuel-sufficiency/guard-sample-cases.txt'
out = sys.argv[1]
rng = random.Random(20261031)
lines = []
summary = []
for d in sorted(os.listdir(root)):
    p = os.path.join(root, d)
    if not os.path.isdir(p):
        continue
    cases = []
    for dp, dn, fn in os.walk(p):
        if 'witness.bin' in fn:
            cases.append(dp)
    cases.sort()
    if not cases:
        continue
    k = len(cases) if len(cases) <= 2000 and d.endswith('warm-originals') else -(-len(cases) // 8)
    pick = sorted(rng.sample(cases, k))
    summary.append((d, len(cases), k))
    lines += pick
fx = [l.strip() for l in open(prev) if l.strip() and '/corpora/' not in l]
fx = [f for f in fx if os.path.isdir(f)]
summary.append(('fixtures', len(fx), len(fx)))
lines += fx
open(out, 'w').write('\n'.join(lines) + '\n')
for s in summary:
    print(*s)
print('total', len(lines))
