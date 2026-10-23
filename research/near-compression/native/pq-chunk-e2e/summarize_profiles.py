#!/usr/bin/env python3
"""Summarize completed run/replay profiles without confusing partial samples with wall time."""
import json
import pathlib
import sys


def summarize(run):
    stages = {}
    for p in sorted((run / 'profiles').glob('*/metadata.json')):
        meta = json.loads(p.read_text())
        samples = p.with_name('resources.jsonl')
        rows = [json.loads(line) for line in samples.read_text().splitlines()] if samples.exists() else []
        stages[p.parent.name] = {
            'wall_s': meta.get('observed_process_wall_s'),
            'exit_code': meta.get('child_exit_code'),
            'covers_process_start': meta['profile_covers_process_start'],
            'sampled_peak_rss_gib': max((r['peak_rss_kb'] for r in rows), default=0) / 1024**2 if rows else None,
            'executable_sha256': meta.get('executable_sha256'),
            'environment': meta.get('environment', {}),
            'perf_command': meta.get('perf_command'),
        }
    failed = {}
    for p in (run / 'failed-profiles').glob('*/metadata.json'):
        m = json.loads(p.read_text())
        failed[p.parent.name] = {'exit_code': m.get('child_exit_code'),
                               'wall_s': m.get('observed_process_wall_s')}
    result = {'run': str(run.resolve()), 'stages': stages, 'failed_attempts': failed}
    complete = bool(stages) and all(s['wall_s'] is not None and s['exit_code'] == 0 and s['covers_process_start'] for s in stages.values())
    result['all_recorded_stages_succeeded'] = complete
    result['summed_stage_wall_s'] = sum(s['wall_s'] for s in stages.values()) if complete else None
    # Excludes inter-stage profiler report generation and orchestration overhead.
    result['proving_wall_s'] = sum(stages[s]['wall_s'] for s in ('base', 'chain')) if all(s in stages and stages[s]['exit_code'] == 0 for s in ('base', 'chain')) else None
    if (run / 'RESULT.json').exists():
        result['packet'] = json.loads((run / 'RESULT.json').read_text())
    return result


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        run = pathlib.Path(arg)
        summary = summarize(run)
        (run / 'TIMINGS.json').write_text(json.dumps(summary, indent=2) + '\n')
        print(json.dumps(summary, indent=2))
