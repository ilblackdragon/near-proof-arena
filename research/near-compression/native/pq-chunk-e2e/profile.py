#!/usr/bin/env python3
"""Profile every proving stage, or attach to an already running prover.

User-space cycles sampled at 19 Hz with DWARF stacks. perf restrictions are handled
with noninteractive sudo when available; global kernel settings are never changed.
/proc resource samples and an explicit profiler status are retained even without perf.
"""
import datetime
import hashlib
import json
import os
import pathlib
import shutil
import signal
import subprocess
import sys
import time
import threading


def main():
    mode, target, *arguments = sys.argv[1:]
    started = time.monotonic()
    if mode == 'run':
        out = pathlib.Path(target)
        assert arguments[0] == '--'
        command = arguments[1:]
        out.mkdir(parents=True, exist_ok=False)
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        def forward_output():
            with (out / 'phase-events.jsonl').open('w') as events:
                for line in child.stdout:
                    sys.stdout.buffer.write(line)
                    sys.stdout.buffer.flush()
                    if any(marker in line for marker in (b'_PHASE', b'_VERIFIED', b'_ANCHOR', b'_OK', b'panicked')):
                        events.write(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                                 'message': line.decode(errors='replace').strip()}) + '\n')
                        events.flush()
        forwarder = threading.Thread(target=forward_output, daemon=True)
        forwarder.start()
        pid = child.pid
    elif mode == 'attach':
        pid = int(target)
        out = pathlib.Path(arguments[0])
        command = pathlib.Path(f'/proc/{pid}/cmdline').read_bytes().replace(b'\0', b' ').decode()
        child = None
        out.mkdir(parents=True, exist_ok=False)
    else:
        raise SystemExit('profile.py run OUT -- COMMAND... | attach PID OUT')
    metadata = {'pid': pid, 'command': command, 'mode': mode, 'sample_hz': 19,
                'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'clock_ticks': os.sysconf('SC_CLK_TCK'),
                'profile_covers_process_start': mode == 'run',
                'environment': {k: v for k, v in os.environ.items()
                                if k in ('RAYON_NUM_THREADS', 'CPUSET', 'HEAVY_MEM',
                                         'NEARPROOF_PQ_DEPS', 'NEARPROOF_DFT_REUSE',
                                         'NEARPROOF_LEAF_DIRECT', 'NEARPROOF_DFT_PAD',
                                         'NEARPROOF_MEMPROF', 'NEARPROOF_CPU_FAST',
                                         'NEARPROOF_DIGEST_BYTES', 'NEARPROOF_COSET_LEAF',
                                         'NEARPROOF_TSTAR', 'NEARPROOF_STREAM_COMMIT',
                                         'NEARPROOF_STREAM_DROP')},
                'load_average_start': list(os.getloadavg())}
    try:
        metadata['cpu_affinity'] = sorted(os.sched_getaffinity(pid))
        shutil.copyfile(f'/proc/{pid}/exe', out / 'executable')
        metadata['executable_sha256'] = hashlib.sha256((out / 'executable').read_bytes()).hexdigest()
        metadata['maps'] = pathlib.Path(f'/proc/{pid}/maps').read_text()
    except OSError as error:
        metadata['identity_error'] = str(error)
    profilers = []
    handles = []
    prefix = None
    for candidate in (['perf'], ['sudo', '-n', 'perf']):
        try:
            probe = subprocess.run(candidate + ['stat', '-e', 'task-clock', '-p', str(pid), '--', 'sleep', '0.05'],
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=5)
            (out / ('probe-' + candidate[0] + '.log')).write_bytes(probe.stdout)
            if probe.returncode == 0:
                prefix = candidate
                break
        except (OSError, subprocess.TimeoutExpired):
            pass
    metadata['perf_command'] = prefix
    if prefix:
        if (out / 'executable').exists():
            cached = subprocess.run(prefix + ['buildid-cache', '-a', str(out / 'executable')],
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (out / 'buildid-cache.log').write_bytes(cached.stdout)
            metadata['buildid_cache_exit_code'] = cached.returncode
        for name, args in [('samples', ['record', '--buildid-mmap', '-F', '19', '-e', 'cycles:u', '--call-graph', 'dwarf,4096',
                                        '-p', str(pid), '-o', str(out / 'perf.data')]),
                           ('counters', ['stat', '-I', '5000', '-x', ',', '-e',
                                         'task-clock,cycles,instructions,cache-misses,branches,branch-misses,context-switches,cpu-migrations,page-faults',
                                         '-p', str(pid)])]:
            log = (out / f'{name}.log').open('wb')
            handles.append(log)
            profilers.append(subprocess.Popen(prefix + args, stdout=log, stderr=log, start_new_session=True))
    else:
        print('PROFILE: perf unavailable; resource sampling only', file=sys.stderr, flush=True)
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    with (out / 'resources.jsonl').open('w') as resources:
        while (child.poll() is None if child else pathlib.Path(f'/proc/{pid}').exists()):
            try:
                stat = pathlib.Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
                if stat[0] == 'Z':
                    break
                status = dict(line.split(':', 1) for line in pathlib.Path(f'/proc/{pid}/status').read_text().splitlines() if ':' in line)
                io = dict(line.split(':', 1) for line in pathlib.Path(f'/proc/{pid}/io').read_text().splitlines())
                sample = {'elapsed_s': round(time.monotonic() - started, 3),
                          'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                          'user_ticks': int(stat[11]), 'system_ticks': int(stat[12]),
                          'rss_kb': int(status.get('VmRSS', '0 kB').split()[0]),
                          'peak_rss_kb': int(status.get('VmHWM', '0 kB').split()[0]),
                          'threads': int(status.get('Threads', '0')),
                          'read_bytes': int(io['read_bytes']), 'write_bytes': int(io['write_bytes'])}
                resources.write(json.dumps(sample) + '\n')
                resources.flush()
            except (OSError, ProcessLookupError):
                break
            if child:
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    pass
            else:
                time.sleep(5)
    metadata['observed_process_wall_s'] = time.monotonic() - started
    metadata['load_average_end'] = list(os.getloadavg())
    for process in profilers:
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGINT)
        try:
            process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
    for handle in handles:
        handle.close()
    metadata['elapsed_profile_s'] = time.monotonic() - started
    metadata['profiler_exit_codes'] = [p.poll() for p in profilers]
    metadata['child_exit_code'] = child.wait() if child else None
    if child:
        forwarder.join(timeout=5)
    if prefix and (out / 'perf.data').exists():
        with (out / 'hotspots.txt').open('wb') as report:
            result = subprocess.run(prefix + ['report', '--stdio', '--no-children', '--sort=dso,symbol',
                                              '--percent-limit', '0.5', '--call-graph', 'none', '-i', str(out / 'perf.data')],
                                    stdout=report, stderr=subprocess.STDOUT)
            metadata['report_exit_code'] = result.returncode
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2))
    return metadata['child_exit_code'] or 0


if __name__ == '__main__':
    sys.exit(main())
