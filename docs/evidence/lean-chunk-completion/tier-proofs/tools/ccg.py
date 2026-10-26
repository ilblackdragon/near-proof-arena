"""Characterize completeCodeGlobal against globalActions (its configuration minus the
complete-code policy) and allFeatures, with the recorded nearcore verdict from meta.json."""
import collections, json, os, sys
W = '/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w12/'


def load(d, t):
    return {json.loads(l)['case']: (json.loads(l)['verdict'], json.loads(l)['reason']) for l in open(W + d + '/' + t + '.jsonl')}


out = {}
for d in ['strat-out', 'w08-out']:
    ccg, ga, af = load(d, 'completeCodeGlobal'), load(d, 'globalActions'), load(d, 'allFeatures')
    tab = collections.Counter()
    samples = collections.defaultdict(list)
    for c, (vc, rc) in ccg.items():
        if c not in ga:
            continue
        vg, rg = ga[c]
        if (vc, rc) == (vg, rg):
            continue
        try:
            nc = json.load(open(c + '/meta.json')).get('nearcore')
        except Exception:
            nc = None
        ncv = 'ok' if nc == 'ok' else ('err' if nc else 'none')
        code_rule = 'w.code_complete' in rc
        k = (vg, vc, code_rule, ncv)
        tab[k] += 1
        if len(samples[k]) < 3:
            samples[k].append(c.replace('/data/illia/nearproof-deps/corpora/', ''))
    out[d] = [{'globalActions': k[0], 'completeCodeGlobal': k[1], 'ccg_reason_is_w.code_complete': k[2],
               'nearcore': k[3], 'n': n, 'examples': samples[k]} for k, n in tab.most_common()]
json.dump(out, open(sys.argv[1], 'w'), indent=1)
for d, rows in out.items():
    print(d)
    for r in rows:
        print('  ', r['n'], r['globalActions'], '->', r['completeCodeGlobal'], 'code_rule' if r['ccg_reason_is_w.code_complete'] else 'OTHER', 'nearcore', r['nearcore'], r['examples'][:1])
