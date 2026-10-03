#!/usr/bin/env python3
"""Local prover benchmark (NOT the judge's measurement).

For each workload dir (oracle `gen --fixtures-layout` output) run `prove` over
every case of the batch sequentially (fresh process per request, like the
judge), `--warmup` untimed batches then `--runs` timed batches; report the
median batch wall time and the median per-request time, for each prover given.
Also checks every claim against expected_claim.bin.

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
print(f"{'workload':<16}{'prover':<22}{'batch':>6}{'median batch ms':>17}{'per-req µs':>12}{'MAD ms':>9}")
for wl in a.workloads:
    cases = sorted(os.path.join(wl, "cases", c) for c in os.listdir(os.path.join(wl, "cases")))
    for name, exe in provers:
        def batch(check=False):
            t0 = time.perf_counter_ns()
            for c in cases:
                r = subprocess.run([exe, "--public", a.public, "--request", c + "/request.bin",
                                    "--witness", c + "/witness.bin", "--claim-out", tmp + "/c",
                                    "--proof-out", tmp + "/p"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                if r.returncode != 0:
                    sys.exit(f"{name} failed on {c}")
                if check and open(tmp + "/c", "rb").read() != open(c + "/expected_claim.bin", "rb").read():
                    sys.exit(f"{name}: claim mismatch on {c}")
            return time.perf_counter_ns() - t0
        batch(check=not exe.endswith("/true"))
        for _ in range(a.warmup):
            batch()
        ts = [batch() for _ in range(a.runs)]
        med = statistics.median(ts)
        mad = statistics.median(abs(t - med) for t in ts)
        print(f"{os.path.basename(wl):<16}{name:<22}{len(cases):>6}{med/1e6:>17.3f}{med/len(cases)/1e3:>12.1f}{mad/1e6:>9.3f}")
