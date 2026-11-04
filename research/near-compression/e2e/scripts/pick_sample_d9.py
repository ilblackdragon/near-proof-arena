"""E2E-D D-9: a random throughput sample of the corpus census (assign.json from classes_d8.py),
mixed classes: N_S / N_M / N_L chunks drawn uniformly without replacement inside each class
(random.Random(SEED)), excluding the D-8 sample members (pick_members_d8.py: each class's largest and
median member). Prints `CLASS NAME CASE_DIR` lines in draw order.

usage: pick_sample_d9.py ASSIGN.json CENSUS_DIR [SEED] [N_S,N_M,N_L]   (default seed 20261104, 6,2,2)
"""
import json, random, sys

a = json.load(open(sys.argv[1]))
census = sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 20261104
quota = [int(x) for x in (sys.argv[4] if len(sys.argv) > 4 else '6,2,2').split(',')]
src = {}
for line in open(census + '/list.txt'):
    k, p = line.split()
    src[k + '_' + p.rstrip('/').split('/')[-1]] = p
nc = a['natural_cells']
rng = random.Random(seed)
for k, q in zip(a['classes'], quota):
    mem = sorted((c for c, kk in a['assign'].items() if kk == k), key=lambda c: (nc[c], c))
    d8 = {mem[-1]} | ({mem[len(mem) // 2]} if len(mem) > 1 else set())
    pool = [c for c in mem if c not in d8]
    for c in rng.sample(pool, min(q, len(pool))):
        print(k, c, src[c])
