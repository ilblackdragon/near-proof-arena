import json
old = '/data/illia/nearproof/.claude/worktrees/agent-a6e1273c00a91e677/research/near-compression/e2e-general/m6/logs/m6-grow-corpus-segcheck.jsonl'
preps = {c['k']: c['prep'] for c in json.load(open('/data/illia/nearproof-deps/e2e-laneA/m6-grow/growcalls.json'))}
for r in sorted(map(json.loads, open(old)), key=lambda r: r['steps']):
    for s in r['segs']:
        if not s['pre'] and s.get('grow', 0) > 0:
            print(r['k'], s['i'], r['K'], r['air'], preps[r['k']], r['steps'])
            raise SystemExit
