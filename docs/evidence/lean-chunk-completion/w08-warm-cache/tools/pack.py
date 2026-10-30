"""Pack the W08 evidence into docs/evidence/lean-chunk-completion/w08-warm-cache/replay."""
import gzip, hashlib, json, shutil, subprocess
from pathlib import Path

W = Path('/tmp/claude-1002/-data-illia-nearproof/e268603b-12da-4c61-ab1c-70f2a15e868f/scratchpad/w08')
S = W.parent
E = Path('/data/illia/nearproof/.claude/worktrees/agent-abdc02168951d8fa3/docs/evidence/lean-chunk-completion/w08-warm-cache')
out = E / 'replay'
out.mkdir(parents=True, exist_ok=True)


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def gz(src, dst):
    data = Path(src).read_bytes().replace(b'/data/illia/nearproof-deps/', b'$DEPS/')
    with gzip.GzipFile(dst, 'wb', mtime=0) as f:
        f.write(data)


summary = {}
for name in ['fam-before-completeCodeGlobal', 'fam-before-allFeatures', 'fam-final-completeCodeGlobal', 'fam-final-allFeatures', 'full805-final-allFeatures', 'full805-final-completeCodeGlobal']:
    rep = json.loads((W / name / 'report.json').read_text())
    summary[name] = {k: rep.get(k) for k in ('status', 'cases', 'verdicts', 'partition', 'package')}
    gz(W / name / 'results.jsonl', out / f'{name}.results.jsonl.gz')
for name in ['uq001-final-allFeatures', 'uq001-final-completeCodeGlobal', 'uq001-full805-allFeatures']:
    shutil.copyfile(W / f'{name}.json', out / f'{name}.json')
for pop, b, a in [('strat886', S / 'strat-before/completeCodeGlobal.jsonl', W / 'c886-final/completeCodeGlobal.jsonl'),
                  ('w08-ccg', S / 'w08-before/completeCodeGlobal.jsonl', W / 'w08-final/completeCodeGlobal.jsonl'),
                  ('w08-af', S / 'w08-before/allFeatures.jsonl', W / 'w08-final/allFeatures.jsonl'),
                  ('strat-ccg', S / 'strat-before/completeCodeGlobal.jsonl', W / 'strat-final/completeCodeGlobal.jsonl')]:
    if not Path(a).exists():
        continue
    r = subprocess.run(['python3', str(W / 'beforeafter.py'), str(b), str(a)], capture_output=True, text=True, check=True)
    summary['transitions-' + pop] = r.stdout.splitlines()
    gz(a, out / f'{pop}-final.jsonl.gz')
    gz(b, out / f'{pop}-before.jsonl.gz')
summary['binaries'] = {'lean_before': sha(S / 'bin-before'), 'lean_draft': sha(S / 'bin-after'),
                       'lean_final': sha(W / 'bin-final'), 'generator': sha(S / 'oracle')}
(out / 'summary.json').write_text(json.dumps(summary, indent=1) + '\n')
print(json.dumps(summary['binaries']))
