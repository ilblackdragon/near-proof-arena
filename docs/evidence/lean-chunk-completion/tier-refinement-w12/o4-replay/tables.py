import json, os, collections, sys

D = '/data/illia/nearproof-deps/w12-o4'
FLAGS = '/data/illia/nearproof/.claude/worktrees/agent-a4c8f20bec2a73f04/docs/evidence/lean-chunk-completion/tier-refinement-w12/flags-replay'


def load(p):
    import gzip
    op = gzip.open if p.endswith('.gz') else open
    out = {}
    with op(p, 'rt') as f:
        for l in f:
            r = json.loads(l)
            out[r.get('case') or r.get('case_dir')] = (r['verdict'], r.get('reason', ''))
    return out


def before_path(pop, tier):
    cands = {
        ('fx', 'runtimeLimits'): f'{D}/fx-runtimeLimits/results.jsonl',
        ('fx', 'storageResolution'): f'{D}/fx-storageResolution/results.jsonl',
        ('slf', 'runtimeLimits'): f'{D}/slf-runtimeLimits/results.jsonl',
        ('slf', 'storageResolution'): f'{D}/slf-storageResolution/results.jsonl',
        ('census', 'runtimeLimits'): f'{D}/census-runtimeLimits/results.jsonl',
        ('census', 'signed'): f'{FLAGS}/census-after-signed.results.jsonl.gz',
        ('slfull', 'runtimeLimits'): f'{D}/slfull-before-runtimeLimits/results.jsonl',
    }
    return cands.get((pop, tier), f'{D}/{pop}B-{tier}/results.jsonl')


def after_path(pop, tier):
    if pop == 'slfull':
        return f'{D}/slfull-after-runtimeLimits/results.jsonl'
    return f'{D}/{pop}A-{tier}/results.jsonl'


rows = []
summary = {}
for pop, tiers in [('fx', ['signed', 'floats', 'protoGas', 'floatsProtoGas', 'genesis', 'genesisFloatsProtoGas',
                           'runtimeLimits', 'storageResolution']),
                   ('slf', ['signed', 'floats', 'protoGas', 'floatsProtoGas', 'genesis', 'genesisFloatsProtoGas',
                            'runtimeLimits', 'storageResolution']),
                   ('census', ['signed', 'runtimeLimits']),
                   ('slfull', ['runtimeLimits'])]:
    for t in tiers:
        b, a = before_path(pop, t), after_path(pop, t)
        if not (os.path.exists(b) and os.path.exists(a)):
            print('missing', pop, t, b if not os.path.exists(b) else a)
            continue
        B, A = load(b), load(a)
        assert set(B) == set(A), (pop, t)
        trans = collections.Counter()
        for k in B:
            if B[k] != A[k]:
                trans[f'{B[k][0]}->{A[k][0]}'] += 1
        va = collections.Counter(v[0] for v in A.values())
        summary[f'{pop}-{t}'] = {'cases': len(B), 'identical': len(B) - sum(trans.values()),
                                 'changed': dict(trans), 'after': dict(va)}
        print(pop, t, len(B), len(B) - sum(trans.values()), dict(trans), dict(va))

# O4 pair after the fix: runtimeLimits vs storageResolution
for pop in ['fx', 'slf', 'census']:
    lo = after_path(pop, 'runtimeLimits')
    hi = after_path(pop, 'storageResolution') if pop != 'census' else f'{D}/census-storageResolution/results.jsonl'
    if not (os.path.exists(lo) and os.path.exists(hi)):
        continue
    L, H = load(lo), load(hi)
    pairs = collections.Counter(f'{L[k][0]}->{H[k][0]}' for k in L)
    viol = [k for k in L if L[k][0] != 'out_of_domain' and L[k] != H[k]]
    summary[f'o4-{pop}'] = {'cases': len(L), 'pairs': dict(pairs), 'violations': len(viol)}
    print('O4', pop, len(L), dict(pairs), 'violations', len(viol))
json.dump(summary, open(f'{D}/summary.json', 'w'), indent=1, sort_keys=True)
