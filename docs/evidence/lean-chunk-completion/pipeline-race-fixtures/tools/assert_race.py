#!/usr/bin/env python3
"""assert_race.py RUNDIR OUT.json : the pipeline-race family's assertions over the replay rows.

A1 (soundness)  no tier accepts a case nearcore rejects (any binary).
A2 (race arm)   with the fixed binary, every case where completeCodeGlobal reports the race exclusion
                is one where globalActions reports the same exclusion (same reason string), and every
                case where the control binary's completeCodeGlobal accepted while globalActions reports
                the race exclusion is reported out of domain by the fixed binary.
A3 (breakage)   the control binary (race arm reverted) violates A2's second clause on >= 1 case.
"""
import collections, json, sys
from pathlib import Path
run = Path(sys.argv[1])
RACE = 'pipelined before the in-chunk deploy'
def load(name):
    return {json.loads(l)['case']: json.loads(l) for l in open(run / name)}
rows = {k: load(f'{k}.jsonl') for k in ['after.completeCodeGlobal', 'control.completeCodeGlobal',
                                         'after.globalActions', 'control.globalActions',
                                         'after.allFeatures', 'control.allFeatures'] if (run / f'{k}.jsonl').exists()}
cases = sorted(rows['after.completeCodeGlobal'])
nc = {c: ('ok' if json.load(open(run / c / 'meta.json'))['nearcore'] == 'ok' else 'err') for c in cases}
out = {'cases': len(cases), 'replays': {}, 'A1_unsound': {}, 'A2_violations': [], 'A3_control_violations': 0}
for k, r in rows.items():
    out['replays'][k] = dict(collections.Counter((r[c]['verdict'], nc[c]) for c in cases).most_common())
    out['replays'][k] = {f'{v}/{n}': x for (v, n), x in collections.Counter((r[c]['verdict'], nc[c]) for c in cases).items()}
    out['A1_unsound'][k] = [c for c in cases if r[c]['verdict'] == 'accept' and nc[c] == 'err']
ccg, ga, ctl = rows['after.completeCodeGlobal'], rows['after.globalActions'], rows['control.completeCodeGlobal']
for c in cases:
    if RACE in ccg[c]['reason'] and ccg[c]['reason'] != ga[c]['reason']:
        out['A2_violations'].append((c, 'ccg race but ga differs', ga[c]['reason'][:120]))
    if ctl[c]['verdict'] == 'accept' and RACE in ga[c]['reason'] and ccg[c]['verdict'] != 'out_of_domain':
        out['A2_violations'].append((c, 'control-accept/ga-race not excluded', ccg[c]['reason'][:120]))
    if ctl[c]['verdict'] == 'accept' and RACE in ga[c]['reason']:
        out['A3_control_violations'] += 1
out['race_arm_cases'] = sum(RACE in ccg[c]['reason'] for c in cases)
out['race_arm_by_nearcore'] = dict(collections.Counter(nc[c] for c in cases if RACE in ccg[c]['reason']))
out['pass'] = (all(not v for v in out['A1_unsound'].values()) and not out['A2_violations']
               and out['A3_control_violations'] > 0)
json.dump(out, open(sys.argv[2], 'w'), indent=1)
print(json.dumps({k: v for k, v in out.items() if k != 'replays'}, indent=1)[:3000])
print(json.dumps(out['replays'], indent=1))
