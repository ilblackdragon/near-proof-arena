#!/usr/bin/env python3
"""Verify a completed source-only build and run exact plus independent axiom audits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--snapshot', type=Path, required=True)
parser.add_argument('--legacy-audits', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--lean', required=True)
args = parser.parse_args()
resource.setrlimit(resource.RLIMIT_AS, (24 * 1024**3, 24 * 1024**3))
snapshot = args.snapshot.resolve()
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((snapshot / 'source-manifest.json').read_text())
modules = {x['module']: x for x in manifest['modules']}
results = json.loads((snapshot / 'results.json').read_text())
assert len(results) == len(modules), 'Build incomplete or duplicate results'
assert {x['module'] for x in results} == set(modules), 'Build result coverage mismatch'
assert all(x['exit_code'] == 0 for x in results), 'Build contains failed modules'
assert not any(p.is_symlink() for p in (snapshot / 'lib').rglob('*')), 'Project library contains symlinks'
audits = {}
for result in results:
    module = result['module']
    rel = Path(*module.split('.'))
    source = (snapshot / 'src' / rel).with_suffix('.lean')
    obj = (snapshot / 'lib' / rel).with_suffix('.olean')
    assert sha(source) == modules[module]['sha256'], 'Source drift: ' + module
    assert sha(obj) == result['olean_sha256'], 'Compiled output drift: ' + module
    if '#guard_msgs' in source.read_text() and '#print axioms' in source.read_text():
        audits[sha(source)] = source
legacy = json.loads((args.legacy_audits / 'manifest.json').read_text())
for item in legacy:
    source = args.legacy_audits / item['file']
    assert sha(source) == item['sha256'], 'Legacy audit source drift: ' + item['file']
    audits.setdefault(item['sha256'], source)
env = dict(os.environ, LEAN_PATH=str(snapshot / 'lib'), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
flags = ['-j1', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
records = []
for index, (digest, source) in enumerate(audits.items()):
    text = source.read_text()
    names = re.findall(r'#print\s+axioms\s+([\w.]+)', text)
    assert names and len(names) == text.count('#guard_msgs'), 'Unexpected audit grammar: ' + str(source)
    # Re-run the original exact expected-output guards against the fresh closure.
    exact = subprocess.run([args.lean] + flags + [str(source.resolve())], env=env,
        cwd=snapshot / 'src', capture_output=True, text=True, timeout=120)
    (out / (str(index) + '-exact.log')).write_text(exact.stdout + exact.stderr)
    assert exact.returncode == 0, 'Exact audit failed: ' + str(source)
    # Independently print actual dependencies, so a guard expecting a forbidden axiom cannot pass.
    imports = '\n'.join(line for line in text.splitlines() if re.match(r'^\s*(?:public\s+)?import\s+', line))
    probe = out / (str(index) + '-axioms.lean')
    probe.write_text(imports + '\n' + '\n'.join('#print axioms ' + name for name in names) + '\n')
    actual = subprocess.run([args.lean] + flags + [str(probe)], env=env,
        cwd=snapshot / 'src', capture_output=True, text=True, timeout=120)
    (out / (str(index) + '-axioms.log')).write_text(actual.stdout + actual.stderr)
    assert actual.returncode == 0, 'Independent axiom probe failed: ' + str(source)
    found = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", actual.stdout)
    assert len(found) == len(names), 'Missing axiom output: ' + str(source)
    for name, line, axioms in found:
        assert name in names, 'Unexpected theorem output: ' + name
        used = {x.strip() for x in axioms.split(',') if x.strip()}
        assert used <= allowed, 'Forbidden axiom: ' + name + ': ' + str(used - allowed)
    records.append({'source': str(source), 'sha256': digest, 'guards': len(names), 'status': 'PASS'})
    (out / 'audit-results.json').write_text(json.dumps(records, indent=2) + '\n')
    print('PASS AUDIT', index + 1, '/', len(audits), source.name, flush=True)
report = {'status': 'PASS', 'source_modules': len(modules), 'audit_files': len(records),
    'exact_axiom_guards': sum(r['guards'] for r in records),
    'allowed_axioms': sorted(allowed), 'source_manifest_sha256': sha(snapshot / 'source-manifest.json'),
    'results_sha256': sha(snapshot / 'results.json'), 'project_olean_symlinks': False,
    'scope': 'Verified frozen source/output hashes, complete successful build coverage, exact audit guards and independent axiom allowlist. This is a certificate for this proof closure, not evidence of the missing global transition theorem or executable prover/judge coverage.'}
(out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report), flush=True)
