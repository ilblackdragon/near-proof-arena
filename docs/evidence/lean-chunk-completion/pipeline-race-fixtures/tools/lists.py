#!/usr/bin/env python3
"""lists.py RUNDIR... : write RUNDIR.all (every case dir) and RUNDIR.calls (cases with a race-round call)."""
import json, sys
from pathlib import Path
for run in sys.argv[1:]:
    run = Path(run)
    alls, calls = [], []
    for meta in sorted(run.glob('*/*/meta.json')):
        d = str(meta.parent)
        alls.append(d)
        s = meta.read_text()
        if 'pipeline-race.' in s and '.call"' in s:
            calls.append(d)
    Path(str(run) + '.all').write_text('\n'.join(alls) + '\n')
    Path(str(run) + '.calls').write_text('\n'.join(calls) + '\n')
    print(run, len(alls), len(calls))
