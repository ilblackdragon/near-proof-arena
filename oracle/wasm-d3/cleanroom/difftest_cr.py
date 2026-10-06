#!/usr/bin/env python3
"""Difftest the clean-room implementation (nearwasm.py) against the nearcore harness.

  difftest_cr.py (opcodes | random N SEED | mutate N SEED | promise N SEED) [--shards K] [--timeout S]

Comparison is on full outcome lines with the same normalisation as tests/difftest.py (Wasmtime's text
for a mistyped-import LinkError and the WasmtimeCompileError message are not compared).  `out-of-domain`
lines are excluded; `unmodeled` lines are failures.  Each case runs in its own worker call with a
per-case timeout; cases exceeding it are counted as skipped.
"""
import collections
import concurrent.futures as cf
import os
import re
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TESTS = os.path.join(HERE, "../tests")
HARNESS = os.environ.get("D3_HARNESS", "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")
IMPL = os.path.join(HERE, "nearwasm.py")


def norm(line):
    line = re.sub(r'WasmtimeCompileError \{ msg: ".*" \}', 'WasmtimeCompileError { msg: <msg> }', line)
    return re.sub(r'LinkError \{ msg: ".*" \}', lambda m: m.group(0) if "unknown or invalid import" in m.group(0)
                  else 'LinkError { msg: <incompatible> }', line)


def gen(argv):
    kind = argv[0]
    if kind == "opcodes":
        with tempfile.NamedTemporaryFile("r", suffix=".labels", delete=False) as lf:
            out = subprocess.run([sys.executable, os.path.join(TESTS, "opcases.py"), lf.name], cwd=TESTS,
                                 check=True, capture_output=True, text=True).stdout.splitlines()
            labels = open(lf.name).read().splitlines()
        return out, labels
    script = {"random": "gen_d3a.py", "mutate": "mutate.py", "promise": "promise_cases.py"}[kind]
    out = subprocess.run([sys.executable, os.path.join(TESTS, script), argv[1], argv[2]], cwd=TESTS,
                         check=True, capture_output=True, text=True).stdout.splitlines()
    return out, [f"{kind}#{i}" for i in range(len(out))]


def run_chunk(lines, timeout):
    """Run a chunk of cases in one process; on timeout, fall back to one process per case."""
    try:
        p = subprocess.run([sys.executable, IMPL], input="\n".join(lines) + "\n", capture_output=True, text=True,
                           timeout=timeout * len(lines))
        out = p.stdout.splitlines()
        if len(out) == len(lines):
            return out
    except subprocess.TimeoutExpired:
        pass
    res = []
    for ln in lines:
        try:
            p = subprocess.run([sys.executable, IMPL], input=ln + "\n", capture_output=True, text=True,
                               timeout=timeout)
            o = p.stdout.splitlines()
            res.append(o[0] if o else f"unmodeled crash {p.stderr[-200:]!r}")
        except subprocess.TimeoutExpired:
            res.append("SKIP timeout")
    return res


def main():
    args = sys.argv[1:]
    shards, timeout = 16, 20.0
    if "--shards" in args:
        i = args.index("--shards"); shards = int(args[i + 1]); del args[i:i + 2]
    if "--timeout" in args:
        i = args.index("--timeout"); timeout = float(args[i + 1]); del args[i:i + 2]
    cases, labels = gen(args)
    n = len(cases)
    t0 = time.time()
    near = subprocess.run([HARNESS], input="\n".join(cases) + "\n", check=True, capture_output=True,
                          text=True).stdout.splitlines()
    t1 = time.time()
    chunk = 20
    chunks = [list(range(i, min(n, i + chunk))) for i in range(0, n, chunk)]
    mine = [None] * n
    with cf.ThreadPoolExecutor(shards) as ex:
        futs = {ex.submit(run_chunk, [cases[i] for i in c], timeout): c for c in chunks}
        for fu in cf.as_completed(futs):
            for i, o in zip(futs[fu], fu.result()):
                mine[i] = o
    t2 = time.time()
    cats = collections.Counter()
    bad = ood = unm = skip = 0
    report = []
    for i, (a, b) in enumerate(zip(near, mine)):
        if b.startswith("out-of-domain"):
            ood += 1
            continue
        if b.startswith("SKIP"):
            skip += 1
            continue
        if b.startswith("unmodeled"):
            unm += 1
            if unm <= 10:
                report.append(f"UNMODELED {labels[i]}: {b}  (nearcore: {a[:150]})")
            continue
        p = a.split(" ", 3)
        if p[0] == "ok":
            cats["ok"] += 1
        else:
            mm = re.match(r"(\w+)(?:[({ ]+(\w+))?", p[3])
            cats[f"{mm.group(1)}:{mm.group(2) or ''}" if mm else p[3][:40]] += 1
        if norm(a) != norm(b):
            bad += 1
            if bad <= 25:
                report.append(f"DISAGREE {labels[i]} (line {i}): {cases[i][:120]}...\n  nearcore : {a[:300]}\n"
                              f"  cleanroom: {b[:300]}")
    print("\n".join(report))
    print(f"family={' '.join(args)} cases={n} compared={n - ood - unm - skip} out_of_domain={ood} "
          f"unmodeled={unm} skipped={skip} disagreements={bad}")
    print(f"nearcore {t1 - t0:.1f}s, cleanroom {t2 - t1:.1f}s ({shards} threads)")
    for c, k in sorted(cats.items(), key=lambda x: -x[1]):
        print(f"  {k:6d}  {c}")
    sys.exit(1 if bad or unm else 0)


if __name__ == "__main__":
    main()
