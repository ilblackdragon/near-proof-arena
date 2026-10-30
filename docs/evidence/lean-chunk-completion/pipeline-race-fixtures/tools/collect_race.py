#!/usr/bin/env python3
"""Collect the pipeline-race family evidence: manifest of every race-arm case (hashes, nearcore
verdict, tier verdicts before/after), a committed selection (one case per run x stratum), and the
assertion report."""
import collections, hashlib, json, shutil, sys
from pathlib import Path
run = Path('/data/illia/nearproof-deps/w12-runs')
ev = Path('/data/illia/nearproof/.claude/worktrees/agent-a5081ae59762de001/docs/evidence/lean-chunk-completion/pipeline-race-fixtures')
RACE = 'pipelined before the in-chunk deploy'
def load(name):
    return {json.loads(l)['case']: json.loads(l) for l in open(run / f'{name}.jsonl')}
R = {k: load(k) for k in ['after.completeCodeGlobal', 'control.completeCodeGlobal', 'after.globalActions',
                          'after.allFeatures']}
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
manifest, sel = [], {}
for c, r in sorted(R['after.completeCodeGlobal'].items()):
    if RACE not in r['reason']:
        continue
    meta = json.loads((run / c / 'meta.json').read_text())
    row = {'case': c, 'nearcore': meta['nearcore'][:200],
           'claim_sha256': sha(run / c / 'claim.bin'), 'witness_sha256': sha(run / c / 'witness.bin'),
           'labels': sorted({l for l in json.dumps(meta.get('tx_labels', {})).split('"') if 'pipeline-race' in l}),
           'completeCodeGlobal_before': R['control.completeCodeGlobal'][c]['verdict'],
           'completeCodeGlobal_after': r['verdict'],
           'globalActions': R['after.globalActions'][c]['verdict'],
           'allFeatures': R['after.allFeatures'][c]['verdict']}
    manifest.append(row)
    key = (c.split('/')[0], c.split('/')[1], meta['nearcore'] == 'ok')
    sel.setdefault(key, c)
ev.mkdir(parents=True, exist_ok=True)
(ev / 'cases').mkdir(exist_ok=True)
index = []
for key, c in sorted(sel.items()):
    dst = ev / 'cases' / c.replace('/', '__')
    if dst.exists():
        shutil.rmtree(dst)
    shutil.copytree(run / c, dst)
    index.append({'dir': dst.name, 'origin': c, 'stratum': f'{key[1]} nearcore={"ok" if key[2] else "err"}'})
json.dump(manifest, open(ev / 'race-arm-manifest.json', 'w'), indent=1)
json.dump(index, open(ev / 'cases' / 'index.json', 'w'), indent=1)
shutil.copy(run / 'race-assert.json', ev / 'race-assert.json')
print(len(manifest), len(index))
print(collections.Counter((m['completeCodeGlobal_before'], m['completeCodeGlobal_after'], m['globalActions'],
                           m['nearcore'] == 'ok') for m in manifest))
