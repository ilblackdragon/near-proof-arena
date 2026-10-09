#!/usr/bin/env python3
"""Freeze committed proof changes plus a prior source closure; rebuild without project oleans."""
import argparse
import concurrent.futures as futures
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--git-dir', required=True)
parser.add_argument('--revision', required=True)
parser.add_argument('--base-revision', required=True)
parser.add_argument('--base-snapshot', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--lean', required=True)
parser.add_argument('--workers', type=int, default=3)
parser.add_argument('--source-root', type=Path, action='append', default=[],
                    help='Additional source-only dependency root, copied and hashed at staging')
args = parser.parse_args()
assert args.workers > 0
out = args.output.resolve()
out.mkdir(parents=True, exist_ok=False)
(out / 'build.py').write_bytes(Path(__file__).read_bytes())
(out / 'invocation.json').write_text(json.dumps(vars(args), default=str, indent=2) + '\n')
git = ['git', '--git-dir=' + args.git_dir]
revision = subprocess.check_output(git + ['rev-parse', args.revision], text=True).strip()
tracked = set(subprocess.check_output(git + ['ls-tree', '-r', '--name-only', revision], text=True).splitlines())
changed = subprocess.check_output(git + ['diff', '--name-only', args.base_revision, revision, '--', '*.lean'], text=True).splitlines()
old = json.loads((args.base_snapshot / 'source-manifest.json').read_text())
old_modules = {r['module']: r for r in old['modules']}
roots = ['zk-formal', 'formal-core', 'spec/lean', 'spec/lean/v3', 'examples/reexec-v3-d0/formal']
target_paths = {}
for path in changed:
    if path not in tracked:
        continue
    for root in ['zk-formal/test'] + roots:
        prefix = root + '/'
        if path.startswith(prefix):
            target_paths[path[len(prefix):-5].replace('/', '.')] = path
            break
    else:
        raise RuntimeError('Unclassified changed Lean source: ' + path)
seen, order, visiting = {}, [], set()
def digest(data):
    return hashlib.sha256(data).hexdigest()
def visit(module):
    if module.split('.')[0] in {'Init', 'Std', 'Lean', 'Lake'}:
        return
    if module in visiting:
        raise RuntimeError('Import cycle: ' + module)
    if module in seen:
        return
    rel = Path(*module.split('.')).with_suffix('.lean')
    candidates = [target_paths[module]] if module in target_paths else []
    candidates += [str(Path(root) / rel) for root in roots]
    source = next((p for p in candidates if p in tracked), None)
    if source is not None:
        data = subprocess.check_output(git + ['show', revision + ':' + source])
        origin = {'kind': 'git', 'revision': revision, 'path': source}
    elif module in old_modules:
        source = str(args.base_snapshot / 'src' / rel)
        data = Path(source).read_bytes()
        if digest(data) != old_modules[module]['sha256']:
            raise RuntimeError('Base snapshot source hash mismatch: ' + module)
        origin = {'kind': 'base-source-snapshot', 'path': source}
    else:
        extra = next((root / rel for root in args.source_root if (root / rel).is_file()), None)
        if extra is None:
            raise RuntimeError('Missing frozen source: ' + module)
        source = str(extra)
        data = extra.read_bytes()
        origin = {'kind': 'additional-source-snapshot', 'path': source}
        if extra.read_bytes() != data:
            raise RuntimeError('Source changed during staging: ' + module)
    imports = []
    for line in data.decode().splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.+)', line)
        if match:
            imports += re.findall(r'[A-Za-z]\w*(?:\.\w+)*', match[1].split('--')[0])
    dest = out / 'src' / rel
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(data)
    seen[module] = {'module': module, 'source': source, 'origin': origin,
                    'sha256': digest(data), 'imports': imports}
    visiting.add(module)
    for dependency in imports:
        visit(dependency)
    visiting.remove(module)
    order.append(module)
for module in list(old_modules) + list(target_paths):
    visit(module)
(out / 'source-manifest.json').write_text(json.dumps({
    'revision': revision, 'base_revision': args.base_revision,
    'base_snapshot': str(args.base_snapshot), 'targets': list(target_paths),
    'modules': [seen[m] for m in order]}, indent=2) + '\n')
(out / 'order.txt').write_text('\n'.join(order) + '\n')
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
