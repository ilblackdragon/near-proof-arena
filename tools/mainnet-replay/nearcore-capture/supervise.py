#!/usr/bin/env python3
"""Run an isolated capture node with disk reserve and export-count stop conditions."""
import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time
import urllib.request


def atomic_json(path, value):
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def allocated(root):
    total = 0
    for base, _, files in os.walk(root):
        for name in files:
            try:
                total += (Path(base) / name).lstat().st_blocks * 512
            except FileNotFoundError:
                pass
    return total


def stop(child):
    if child.poll() is not None:
        return
    os.killpg(child.pid, signal.SIGTERM)
    try:
        child.wait(timeout=60)
    except subprocess.TimeoutExpired:
        os.killpg(child.pid, signal.SIGKILL)
        child.wait()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--binary', type=Path, required=True)
    p.add_argument('--home', type=Path, required=True)
    p.add_argument('--exports', type=Path, required=True)
    p.add_argument('--rpc', default='http://127.0.0.1:3038/status')
    p.add_argument('--reserve-gib', type=int, default=15)
    p.add_argument('--max-data-gib', type=int, default=35)
    p.add_argument('--max-captures', type=int, default=1200)
    p.add_argument('--interval', type=int, default=15)
    a = p.parse_args()
    if min(a.reserve_gib, a.max_data_gib, a.max_captures, a.interval) <= 0:
        p.error('budgets, target and interval must be positive')
    a.home.mkdir(parents=True, exist_ok=True)
    a.exports.mkdir(parents=True, exist_ok=True)
    env = os.environ | {'NEAR_W13_EXPORT_DIR': str(a.exports.resolve()),
                        'RAYON_NUM_THREADS': '8', 'RUST_LOG': 'warn,near=info,stats=info,client=info'}
    child = None
    reason = 'starting'
    status = {}
    def interrupted(*_):
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        if shutil.disk_usage(a.home).free < a.reserve_gib * 2**30:
            reason = 'disk reserve reached before launch'
            return
        with (a.home / 'node.log').open('ab', buffering=0) as log:
            child = subprocess.Popen([str(a.binary), '--home', str(a.home), 'run'],
                                     stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
            while child.poll() is None:
                captures = list(a.exports.glob('*/capture.json'))
                verdicts = []
                for path in a.exports.glob('*/native-validation.json'):
                    try: verdicts.append(json.loads(path.read_text()).get('verdict'))
                    except (OSError, ValueError): pass
                free = shutil.disk_usage(a.home).free
                used = allocated(a.home)
                status = dict(state='running', pid=child.pid, updated_unix=time.time(),
                              captures=len(captures), native_accepts=verdicts.count('accept'),
                              native_rejects=verdicts.count('reject'), free_bytes=free, home_allocated_bytes=used)
                try:
                    with urllib.request.urlopen(a.rpc, timeout=3) as r:
                        node = json.load(r)
                    status['node'] = {k: node.get(k) for k in ('chain_id', 'protocol_version', 'sync_info')}
                except Exception as exc:
                    status['rpc_error'] = str(exc)
                atomic_json(a.home / 'capture-status.json', status)
                node_status = status.get('node', {})
                if node_status.get('sync_info', {}).get('syncing') is False and node_status.get('protocol_version') != 86:
                    reason = 'synced node is outside pinned PV86'; break
                if free < a.reserve_gib * 2**30:
                    reason = 'disk reserve reached'; break
                if used > a.max_data_gib * 2**30:
                    reason = 'data budget reached'; break
                if len(captures) >= a.max_captures:
                    reason = 'capture target reached'; break
                time.sleep(a.interval)
            else:
                reason = f'node exited {child.returncode}'
    except KeyboardInterrupt:
        reason = 'operator stop'
    finally:
        if child is not None:
            stop(child)
        atomic_json(a.home / 'capture-status.json', status | {'state': 'stopped', 'reason': reason,
                    'updated_unix': time.time(), 'exit_code': child.returncode if child else None})


if __name__ == '__main__':
    main()
