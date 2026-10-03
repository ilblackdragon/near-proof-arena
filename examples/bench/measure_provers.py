#!/usr/bin/env python3
"""Local prover benchmark (NOT the judge's measurement).

For each workload dir (oracle `gen --fixtures-layout` output) and each prover:
run `prove` over every case of the batch sequentially, one fresh process per
request (as the judge does). The provers are INTERLEAVED batch by batch so
machine-load drift affects them equally. `--warmup` untimed rounds, then
`--runs` timed rounds; reports median and minimum batch wall time and the
median per-request time. The first round also checks every claim against
expected_claim.bin.

usage: measure_provers.py --prover NAME=PATH ... --public DIR WORKLOAD_DIR...
"""
import argparse, os, statistics, subprocess, sys, tempfile, time

ap = argparse.ArgumentParser()
ap.add_argument("--prover", action="append", required=True)
ap.add_argument("--public", required=True)
ap.add_argument("--warmup", type=int, default=3)
ap.add_argument("--runs", type=int, default=15)
ap.add_argument("workloads", nargs="+")
a = ap.parse_args()
provers = [p.split("=", 1) for p in a.prover]
tmp = tempfile.mkdtemp()


def batch(name, exe, cases, check):
    t0 = time.perf_counter_ns()
    for c in cases:
        r = subprocess.run([exe, "--public", a.public, "--request", c + "/request.bin",
                            "--witness", c + "/witness.bin", "--claim-out", tmp + "/c",
                            "--proof-out", tmp + "/p"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if check and (r.returncode != 0 or open(tmp + "/c", "rb").read() != open(c + "/expected_claim.bin", "rb").read()):
            sys.exit(f"{name}: wrong result on {c}")
    return time.perf_counter_ns() - t0


print(f"{'workload':<14}{'prover':<14}{'batch':>6}{'median ms':>11}{'min ms':>9}{'per-req µs':>12}{'MAD ms':>9}")
for wl in a.workloads:
    cases = sorted(os.path.join(wl, "cases", c) for c in os.listdir(os.path.join(wl, "cases")))
    ts = {n: [] for n, _ in provers}
    for rnd in range(a.warmup + a.runs):
        for name, exe in provers:
            t = batch(name, exe, cases, check=(rnd == 0 and not exe.endswith("/true")))
            if rnd >= a.warmup:
                ts[name].append(t)
    for name, _ in provers:
        med = statistics.median(ts[name])
        mad = statistics.median(abs(t - med) for t in ts[name])
        print(f"{os.path.basename(wl):<14}{name:<14}{len(cases):>6}{med/1e6:>11.3f}{min(ts[name])/1e6:>9.3f}"
              f"{med/len(cases)/1e3:>12.1f}{mad/1e6:>9.3f}")
