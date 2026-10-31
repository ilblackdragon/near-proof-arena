"""Collect one e2e run into results/<name>.json and an sha256 evidence manifest.

usage: collect.py RUN_DIR OUT_DIR
"""
import hashlib, json, pathlib, re, sys

run, out = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
name = run.name
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def peak_gib(stage):
    f = run / 'profiles' / stage / 'resources.jsonl'
    if not f.exists():
        return None
    peaks = [json.loads(l).get('peak_rss_kb', 0) for l in f.read_text().splitlines() if l.strip()]
    return round(max(peaks) / 2**20, 2) if peaks else None

stages = {}
for l in (run / 'STAGES.txt').read_text().splitlines() if (run / 'STAGES.txt').exists() else []:
    m = re.match(r'STAGE (\S+) wall_s=([\d.]+)', l)
    if m:
        stages[m[1]] = {'wall_s': round(float(m[2]), 2), 'peak_rss_gib': peak_gib(m[1])}
levels = []
chain = (run / 'chain.log').read_text() if (run / 'chain.log').exists() else ''
for m in re.finditer(r'(L\d+)_VERIFIED rows=(\d+) shapes=(\[[^\]]*\]) bytes=(\d+) seconds=([\d.]+)', chain):
    levels.append({'level': m[1], 'program_rows': int(m[2]), 'shapes': m[3], 'proof_bytes': int(m[4]), 'prove_s': float(m[5])})
fm = re.search(r'FINAL_PHASE proved_and_verified seconds=([\d.]+)', chain)
base = (run / 'base.log').read_text() if (run / 'base.log').exists() else ''
bm = re.search(r'BASE_PROOF total=(\d+)', base)
res = json.loads((run / 'RESULT.json').read_text()) if (run / 'RESULT.json').exists() else {}
vlog = (run / 'verify.log').read_text() if (run / 'verify.log').exists() else ''
vp = re.search(r'VERIFY_PROFILE_MS (.*)', vlog)
neg = json.loads((run / 'NEGATIVES.json').read_text()) if (run / 'NEGATIVES.json').exists() else {}
row = {
    'run': name,
    'case_inputs': json.loads((run / 'RUN.json').read_text()).get('inputs', {}) if (run / 'RUN.json').exists() else {},
    'env': json.loads((run / 'RUN.json').read_text()).get('env', {}) if (run / 'RUN.json').exists() else {},
    'base_proof_bytes': int(bm[1]) if bm else None,
    'levels': levels,
    'final_prove_s': float(fm[1]) if fm else None,
    'result': res,
    'stages': stages,
    'verify_profile_ms': dict(kv.split('=') for kv in vp[1].split()) if vp else None,
    'verify_ok': 'INDEPENDENT_VERIFY_OK' in vlog,
    'negatives': {k: ('PASS' if v['pass'] else 'FAIL') + f" ({'accepted' if v['accepted'] else 'rejected'})" for k, v in neg.items()},
}
(out / f'{name}.json').write_text(json.dumps(row, indent=1) + '\n')
files = ['FINAL.bundle', 'FINAL.proof', 'SETUP.json', 'SETUP.sha256', 'RESULT.json', 'BASE.proof', 'BASE.u.json',
         'hint.bin', 'RUN.json', 'STAGES.txt', 'NEGATIVES.json', 'base.log', 'chain.log', 'verify.log',
         'dump/claim.bin', 'dump/pubs.bin', 'public/pubs.bin', 'tools/prover', 'tools/statepublic', 'tools/statedump'] + \
        [f'L{i}.proof' for i in range(1, 11)]
manifest = {f: {'bytes': (run / f).stat().st_size, 'sha256': sha(run / f)} for f in files if (run / f).exists()}
(out / f'{name}.manifest.json').write_text(json.dumps({'run_dir': str(run), 'files': manifest}, indent=1) + '\n')
print(json.dumps({k: row[k] for k in ('run', 'base_proof_bytes', 'final_prove_s', 'verify_ok')}), row['result'].get('bundle_bytes'))
