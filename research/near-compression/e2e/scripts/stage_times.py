"""Wall time and sampled peak RSS of each profiled stage of a run dir (profile.py layout).
usage: stage_times.py RUN_DIR..."""
import json, pathlib, sys
for run in map(pathlib.Path, sys.argv[1:]):
    for st in sorted((run / 'profiles').iterdir()) if (run / 'profiles').exists() else []:
        try:
            m = json.loads((st / 'metadata.json').read_text())
            rss = [json.loads(l).get('peak_rss_kb', 0) for l in (st / 'resources.jsonl').read_text().splitlines() if l.strip()]
            print(run.name, st.name, 'wall_s=%.1f' % m.get('observed_process_wall_s', -1), 'peak_rss_gib=%.2f' % (max(rss + [0]) / 2**20))
        except Exception as e:
            print(run.name, st.name, 'n/a', e)
