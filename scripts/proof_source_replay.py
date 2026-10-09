#!/usr/bin/env python3
"""Rebuild an extracted proof source snapshot without git or prebuilt project dependencies."""
import argparse
import concurrent.futures as futures
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import time
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--snapshot', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--lean', required=True)
parser.add_argument('--workers', type=int, default=3)
args = parser.parse_args()
assert args.workers > 0
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
manifest = json.loads((args.snapshot / 'source-manifest.json').read_text())
seen = {r['module']: r for r in manifest['modules']}
order = [r['module'] for r in manifest['modules']]
target_paths = manifest.get('targets', [])
def digest(data):
    return hashlib.sha256(data).hexdigest()
for module in order:
    rel = Path(*module.split('.')).with_suffix('.lean')
    data = (args.snapshot / 'src' / rel).read_bytes()
    if digest(data) != seen[module]['sha256']:
        raise RuntimeError('Snapshot source hash mismatch: ' + module)
    dest = out / 'src' / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
(out / 'source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
lib, logs = out / 'lib', out / 'logs'
lib.mkdir(); logs.mkdir()
env = dict(os.environ, LEAN_PATH=str(lib), LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH', None)
flags = ['-j1', '-DautoImplicit=false', '-DrelaxedAutoImplicit=false']
(out / 'environment.json').write_text(json.dumps({
    'lean': args.lean, 'lean_version': subprocess.check_output([args.lean, '--version'], text=True).strip(),
    'LEAN_PATH': str(lib), 'flags': flags, 'workers': args.workers,
    'reused_project_oleans': False, 'timeout_seconds': 600,
    'per_process_address_space_bytes': 24 * 1024**3}, indent=2) + '\n')
print('STAGED', len(order), 'modules;', len(target_paths), 'changed targets; no reused project oleans', flush=True)
def limit():
    resource.setrlimit(resource.RLIMIT_AS, (24 * 1024**3, 24 * 1024**3))
def build(module):
    if shutil.disk_usage(out).free < 4 * 1024**3:
        raise RuntimeError('Disk reserve below 4 GiB')
    rel = Path(*module.split('.'))
    source = (out / 'src' / rel).with_suffix('.lean')
    obj = (lib / rel).with_suffix('.olean')
    obj.parent.mkdir(parents=True, exist_ok=True)
    log = logs / (module + '.log')
    start = time.monotonic()
    try:
        with log.open('wb') as stream:
            result = subprocess.run([args.lean] + flags + ['-o', str(obj), str(source)],
                cwd=out / 'src', env=env, stdout=stream, stderr=subprocess.STDOUT,
                preexec_fn=limit, timeout=600)
        code = result.returncode
    except subprocess.TimeoutExpired:
        code = 124
    return {'module': module, 'exit_code': code, 'seconds': round(time.monotonic()-start, 3),
            'log': str(log), 'olean_sha256': digest(obj.read_bytes()) if code == 0 else None}
pending, running, passed, results = list(order), {}, set(), []
failed = False
with futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
    while pending or running:
        for module in pending[:]:
            if len(running) >= args.workers or failed:
                break
            if all(d not in seen or d in passed for d in seen[module]['imports']):
                pending.remove(module)
                running[pool.submit(build, module)] = module
        if not running:
            raise RuntimeError('Unresolved dependencies or failed build')
        done, _ = futures.wait(running, return_when=futures.FIRST_COMPLETED)
        for future in done:
            module = running.pop(future)
            result = future.result()
            results.append(result)
            (out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
            if result['exit_code']:
                failed = True
                print('FAIL', module, Path(result['log']).read_text()[-8000:], flush=True)
            else:
                passed.add(module)
                print('PASS', len(passed), '/', len(order), module, flush=True)
        if failed and not running:
            raise SystemExit(1)
print('COMPLETE', len(passed), 'source modules; global transition completion is a separate gate', flush=True)
