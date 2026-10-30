#!/usr/bin/env python3
"""Before/after verdict identity of two successor checkers on one population (W02/W16).

`run`: run CHECKER on every case (batches of `--batch` cases per process, `--jobs` processes) and
write `results.jsonl` (case, verdict, reason) plus wall time. Unlike `replay_successor.py` this
needs no nearcore expectation in `meta.json`, so it covers every committed case directory.
`diff`: compare two results files case by case on verdict and reason.

  verdict_identity.py run --checker BIN --tier allFeatures --cases-file LIST --out RES.jsonl [--jobs N]
  verdict_identity.py diff BEFORE.jsonl AFTER.jsonl [--out DIFF.json]
"""
import argparse
import collections
import hashlib
import json
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path


def run_batch(checker, tier, part, timeout):
    try:
        r = subprocess.run([checker, "--tier", tier, *part], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return [{"case": c, "verdict": "timeout", "reason": ""} for c in part]
    rows = {}
    for line in r.stdout.splitlines():
        try:
            o = json.loads(line)
        except json.JSONDecodeError:
            continue
        rows[o["case"]] = {"case": o["case"], "verdict": o["verdict"], "reason": o["reason"]}
    out = []
    for c in part:
        out.append(rows.get(c, {"case": c, "verdict": "error", "reason": f"exit {r.returncode}: {r.stderr[-300:]}"}))
    return out


def cmd_run(a):
    cases = [l for l in Path(a.cases_file).read_text().splitlines() if l.strip()]
    batches = [cases[i:i + a.batch] for i in range(0, len(cases), a.batch)]
    t0 = time.time()
    with ThreadPoolExecutor(a.jobs) as ex:
        res = [row for part in ex.map(lambda p: run_batch(a.checker, a.tier, p, a.timeout), batches) for row in part]
    wall = time.time() - t0
    Path(a.out).write_text("".join(json.dumps(r, sort_keys=True) + "\n" for r in res))
    meta = {"checker": a.checker, "checker_sha256": hashlib.sha256(Path(a.checker).read_bytes()).hexdigest(),
            "tier": a.tier, "cases": len(cases), "jobs": a.jobs, "wall_s": round(wall, 1),
            "verdicts": dict(collections.Counter(r["verdict"] for r in res))}
    Path(a.out + ".meta.json").write_text(json.dumps(meta, indent=1) + "\n")
    print(json.dumps(meta))


def load(p):
    return {json.loads(l)["case"]: json.loads(l) for l in Path(p).read_text().splitlines() if l.strip()}


def cmd_diff(a):
    b, c = load(a.before), load(a.after)
    if set(b) != set(c):
        print(f"populations differ: {len(set(b) ^ set(c))} cases", file=sys.stderr)
    common = sorted(set(b) & set(c))
    vdiff = [k for k in common if b[k]["verdict"] != c[k]["verdict"]]
    rdiff = [k for k in common if b[k]["verdict"] == c[k]["verdict"] and b[k]["reason"] != c[k]["reason"]]
    bad = [k for k in common if b[k]["verdict"] in ("error", "timeout") or c[k]["verdict"] in ("error", "timeout")]
    out = {"cases": len(common), "identical_verdict_and_reason": len(common) - len(vdiff) - len(rdiff),
           "verdict_changes": len(vdiff), "reason_changes": len(rdiff), "errors_or_timeouts": len(bad),
           "before": dict(collections.Counter(b[k]["verdict"] for k in common)),
           "after": dict(collections.Counter(c[k]["verdict"] for k in common)),
           "examples": [{"case": k, "before": b[k], "after": c[k]} for k in (vdiff + rdiff)[:20]]}
    if a.out:
        Path(a.out).write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out, indent=1))
    return 1 if (vdiff or rdiff or bad) else 0


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    r = sp.add_parser("run")
    r.add_argument("--checker", required=True)
    r.add_argument("--tier", default="allFeatures")
    r.add_argument("--cases-file", required=True)
    r.add_argument("--out", required=True)
    r.add_argument("--jobs", type=int, default=8)
    r.add_argument("--batch", type=int, default=100)
    r.add_argument("--timeout", type=int, default=7200)
    d = sp.add_parser("diff")
    d.add_argument("before")
    d.add_argument("after")
    d.add_argument("--out")
    a = ap.parse_args()
    if a.cmd == "run":
        cmd_run(a)
    else:
        sys.exit(cmd_diff(a))


if __name__ == "__main__":
    main()
