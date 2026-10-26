"""P2: the strata where tiers differ (every ood-corpus case and every gap mutant), from strat.txt
plus the allFeatures/signed census rows: a strat case is in P2 if it is in an `ood` dir, or the
signed and allFeatures verdicts differ."""
import json
S = '/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w12/'
def load(t):
    return {json.loads(l)['case']: json.loads(l)['verdict'] for l in open(S + f'strat-out/{t}.jsonl')}
a, s = load('allFeatures'), load('signed')
cases = [c for c in open(S + 'strat.txt').read().split()]
p2 = [c for c in cases if c.split('/')[6] == 'ood' or a[c] != s[c] or a[c] == 'out_of_domain']
open(S + 'p2.txt', 'w').write('\n'.join(p2) + '\n')
print(len(p2))
