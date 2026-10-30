import gzip, json, os, collections
d = '/data/illia/nearproof/.claude/worktrees/agent-a994ce707a5fba315/docs/evidence/lean-chunk-completion/tier-refinement-w12/o4-replay'
pats = {
    'G1 RecordedStorageExceeded': 'RecordedStorageExceeded',
    'G2 w.fuel_certificate': 'fuel_certificate',
    'G3 e.code_prep_race': 'code_prep_race',
    'G4 buffered gas left': 'buffered receipts gas left',
    'G5 legacy wallet / pre-PV83': 'wallet',
    'legacy MissingTrieValue (contract code)': 'MissingTrieValue (contract code)',
}
def load(p):
    out = {}
    for l in gzip.open(p, 'rt'):
        r = json.loads(l)
        out[r.get('case') or r.get('case_dir')] = r
    return out
res = {}
for pop in ['fx', 'census', 'slf']:
    lo = load(f'{d}/{pop}-runtimeLimits.results.jsonl.gz')
    hi = load(f'{d}/{pop}-storageResolution.results.jsonl.gz')
    row = {'cases': len(hi), 'legacy_decided': sum(1 for k in lo if lo[k]['verdict'] != 'out_of_domain')}
    for name, pat in pats.items():
        row[name + ' (storageResolution, any)'] = sum(1 for r in hi.values() if pat in (r.get('reason') or ''))
        row[name + ' (storageResolution, legacy decided)'] = sum(
            1 for k, r in hi.items() if pat in (r.get('reason') or '') and lo[k]['verdict'] != 'out_of_domain')
        row[name + ' (runtimeLimits, any)'] = sum(1 for r in lo.values() if pat in (r.get('reason') or ''))
    res[pop] = row
print(json.dumps(res, indent=1))
