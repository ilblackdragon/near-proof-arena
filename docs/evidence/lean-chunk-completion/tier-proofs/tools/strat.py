"""Stratified census population: every `ood` case, every gap case (nearcore ok and not RelD3 per
meta), every case whose meta carries a genesis/resharding/global/curve marker, and a seeded 5% of the
rest. Writes strat.txt and strat-strata.json."""
import json, os, random, collections
S = '/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w12'
L = open(S + '/all_cases.txt').read().split()
random.seed(20261026)
pick, strata = [], collections.Counter()
for c in L:
    sub = c.split('/')[6]
    why = None
    if sub == 'ood':
        why = 'ood'
    else:
        try:
            m = json.load(open(c + '/meta.json'))
        except Exception:
            m = {}
        if m.get('nearcore') == 'ok' and m.get('expected_rel_d3') is False:
            why = 'gap'
    if why is None and random.random() < 0.05:
        why = 'random5'
    if why:
        pick.append(c)
        strata[why] += 1
open(S + '/strat.txt', 'w').write('\n'.join(pick) + '\n')
json.dump({'total_population': len(L), 'picked': len(pick), 'strata': strata, 'seed': 20261026},
          open(S + '/strat-strata.json', 'w'), indent=1)
print(len(pick), dict(strata))
