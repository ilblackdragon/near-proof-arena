#!/usr/bin/env python3
"""Run a successor checker on cases one process each, recording verdict, wall time and max RSS
(W02/W16 per-chunk budget). Cases run sequentially unless `--jobs` > 1; the host load average is
recorded before and after every case, since wall time on a shared host is an upper bound.

  python3 tools/d3/time_cases.py --checker BIN [--tier allFeatures] --cases-file LIST --out OUT.json \
      [--timeout S] [--jobs N]
"""
import argparse
import hashlib
import json
import os
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def run(checker, tier, case, timeout):
    load0 = os.getloadavg()[0]
    t0 = time.time()
    try:
        r = subprocess.run(["/usr/bin/time", "-f", "MAXRSS %M CPU %U %S", checker, "--tier", tier, case],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"case": case, "verdict": "timeout", "wall_s": timeout, "load": [load0, os.getloadavg()[0]]}
    wall = time.time() - t0
    rl = next((l.split() for l in r.stderr.splitlines() if l.startswith("MAXRSS ")), None)
    rss = int(rl[1]) * 1024 if rl else None
    cpu = round(float(rl[3]) + float(rl[4]), 2) if rl else None
    row = {"case": case, "wall_s": round(wall, 2), "cpu_s": cpu, "max_rss": rss, "load": [round(load0, 1), round(os.getloadavg()[0], 1)]}
    try:
        out = json.loads(r.stdout.strip().splitlines()[-1])
        row.update(verdict=out["verdict"], reason=out["reason"])
    except Exception:
        row.update(verdict="error", reason=(r.stderr or r.stdout)[-400:])
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--checker", required=True)
    ap.add_argument("--tier", default="allFeatures")
    ap.add_argument("--cases-file", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--timeout", type=int, default=6 * 3600)
    ap.add_argument("--jobs", type=int, default=1)
    a = ap.parse_args()
    cases = [l for l in Path(a.cases_file).read_text().splitlines() if l.strip()]
    with ThreadPoolExecutor(a.jobs) as ex:
        rows = list(ex.map(lambda c: run(a.checker, a.tier, c, a.timeout), cases))
    for r in rows:
        print(json.dumps(r))
    out = {"checker": a.checker, "checker_sha256": hashlib.sha256(Path(a.checker).read_bytes()).hexdigest(),
           "tier": a.tier, "rows": rows}
    Path(a.out).write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
