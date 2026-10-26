"""Census summary for docs/evidence/lean-chunk-completion/tier-proofs.

usage: summarize.py OUT_JSON VIOLATIONS_JSONL
Populations:
  P2     — every case of the stratified population in an `ood` corpus dir or where signed and
           allFeatures differ or allFeatures excludes (7,178); all 13 tiers.
  STRAT  — the full stratified population (18,553); the tiers run on all of it.
  FULL   — every case of the six corpora (235,716), for the tiers run on all of them.
  FX     — the 461 cases of the committed fixture sets (docs/evidence/lean-chunk-completion/*-fixtures).
  MAINNET — the 1,223 mainnet shard-13 chunks of mainnet-w13-shard13 (heights 221489407-221490629).
  SANITY_MERGED — 5,765 cases (3,000 seeded random, 1,000 of P2, W08, FX, MAINNET) on the checker
           built after merging main f68a56f5c (allFeatures: no gas bound, witness/layout lifts).
  W08    — the 103 code mutants whose allFeatures verdict changed with the W08 pipeline rule; all 13 tiers.
For every ordered tier pair (lo, hi): cases where lo decides (accept/reject) and hi's result
differs (verdict, or reason string for the same verdict).
"""
import collections, json, os, re, sys

W = '/tmp/claude-1002/-data-illia-nearproof/0e65db12-f071-4aee-abe1-6a3d8ed8412f/scratchpad/w12/'
out_json, viol_out = sys.argv[1:3]
TIERS = ['signed', 'floats', 'protoGas', 'floatsProtoGas', 'genesis', 'genesisFloatsProtoGas',
         'runtimeLimits', 'storageResolution', 'globalActions', 'completeCodeGlobal', 'curveHosts',
         'resharding', 'allFeatures']
CFG = {
    'signed': set(), 'floats': {'floats'}, 'protoGas': {'gas'}, 'floatsProtoGas': {'floats', 'gas'},
    'genesis': {'genesis'}, 'genesisFloatsProtoGas': {'floats', 'gas', 'genesis'},
    'runtimeLimits': {'floats', 'gas', 'genesis', 'loadingLimits'},
    'storageResolution': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution'},
    'globalActions': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution', 'globalActions'},
    'completeCodeGlobal': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution', 'globalActions',
                           'completeCodeWitness'},
    'curveHosts': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution', 'curveHosts'},
    'resharding': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution', 'curveHosts', 'resharding'},
    'allFeatures': {'floats', 'gas', 'genesis', 'loadingLimits', 'storageResolution', 'globalActions',
                    'curveHosts', 'resharding', 'segmentUnbounded', 'witnessUnbounded', 'layoutUnbounded',
                    'gasNone'},
}
PROVED = {('signed', 'protoGas'): 'relSuccessor_protoGas_mono',
          ('floats', 'floatsProtoGas'): 'relSuccessor_floatsProtoGas_mono',
          ('signed', 'genesis'): 'relSuccessor_genesis_mono',
          ('floatsProtoGas', 'genesisFloatsProtoGas'): 'relSuccessor_genesisFloatsProtoGas_mono'}


def load(d, t):
    p = W + d + '/' + t + '.jsonl'
    if not os.path.exists(p):
        return None
    r = {}
    for l in open(p):
        j = json.loads(l)
        r[j['case']] = (j['verdict'], j['reason'])
    return r


def short(c):
    return c.replace('/data/illia/nearproof-deps/corpora/', '').replace('/data/illia/nearproof/.claude/worktrees/agent-a79dafeb8f1dcd80c/', '').replace('/data/illia/nearproof-deps/mainnet-w13/replay-cases/', 'mainnet-w13/')


def norm(s):
    return re.sub(r'\d+', 'N', s)[:200]


def pop(name, d, cases, tiers):
    V = {t: load(d, t) for t in tiers}
    V = {t: v for t, v in V.items() if v is not None and all(c in v for c in cases)}
    tiers = [t for t in tiers if t in V]
    res = {'cases': len(cases), 'tiers': tiers,
           'verdicts': {t: dict(collections.Counter(V[t][c][0] for c in cases)) for t in tiers},
           'pairs': []}
    viols = []
    for lo in tiers:
        for hi in tiers:
            if lo == hi:
                continue
            vv, rr = collections.Counter(), 0
            kept = 0
            for c in cases:
                va, ra = V[lo][c]
                vb, rb = V[hi][c]
                if va in ('accept', 'reject') and (va, ra) != (vb, rb):
                    if va != vb:
                        vv[(va, vb, norm(ra), norm(rb))] += 1
                    else:
                        rr += 1
                    kept += 1
                    if CFG[lo] <= CFG[hi] and kept <= 200:
                        viols.append({'population': name, 'lo': lo, 'hi': hi, 'case': short(c), 'lo_verdict': va, 'lo_reason': ra, 'hi_verdict': vb, 'hi_reason': rb})
            res['pairs'].append({'lo': lo, 'hi': hi, 'flags_contained': CFG[lo] <= CFG[hi],
                                 'proved': PROVED.get((lo, hi)),
                                 'verdict_violations': sum(vv.values()), 'reason_only': rr,
                                 'classes': [{'n': n, 'lo': k[0], 'hi': k[1], 'lo_reason': k[2], 'hi_reason': k[3]}
                                             for k, n in vv.most_common(10)]})
    return res, viols


import sys as _s
ONLY = _s.argv[3].split(',') if len(_s.argv) > 3 else None
p2 = open(W + 'p2.txt').read().split()
strat = open(W + 'strat.txt').read().split()
w08 = open(W + 'w08.txt').read().split()
full = open(W + 'all_cases.txt').read().split() if os.path.exists(W + 'all_cases.txt') else []
fx = open(W + 'fixtures.txt').read().split()
mn = open(W + 'mainnet.txt').read().split()
san = open(W + 'sanity.txt').read().split()
summary, allv = {}, []
for name, d, cases in [('P2', 'strat-out', p2), ('STRAT', 'strat-out', strat), ('W08', 'w08-out', w08), ('FULL', 'full-out', full), ('FX', 'fx-out', fx), ('MAINNET', 'mn-out', mn), ('SANITY_MERGED', 'sanity-out', san)]:
    if ONLY and name not in ONLY:
        continue
    r, v = pop(name, d, cases, TIERS)
    summary[name] = r
    allv += v
json.dump(summary, open(out_json, 'w'), indent=1)
with open(viol_out, 'w') as f:
    for v in allv:
        f.write(json.dumps(v) + '\n')
for name, r in summary.items():
    print(f'== {name}: {r["cases"]} cases, tiers {len(r["tiers"])}')
    for p in r['pairs']:
        if p['verdict_violations'] or p['reason_only']:
            print(f"   {'C' if p['flags_contained'] else ' '} {p['lo']:>22} -> {p['hi']:<22} "
                  f"viol {p['verdict_violations']:5d} reason-only {p['reason_only']:5d}")
    nz = sum(1 for p in r['pairs'] if p['flags_contained'] and p['lo'] != 'completeCodeGlobal'
             and p['hi'] != 'completeCodeGlobal' and (p['verdict_violations'] or p['reason_only']))
    print('   contained pairs (excluding completeCodeGlobal) with any violation:', nz)
