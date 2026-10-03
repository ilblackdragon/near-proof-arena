#!/usr/bin/env python3
"""Local measurement (NOT the judge's measurement) of candidate packages on
the challenge's workload classes.

usage: run-bench.py --prover NAME=OUT_DIR [--prover ...] --params params.bin
                    [--cpus 0-7] [--warmup 1] [--runs 5] [--verify-runs 5]
                    [--only-first N] WORKLOAD_DIR...

Each WORKLOAD_DIR is `near-arena-oracle gen --fixtures-layout` output
(`cases/<name>/{request,witness,expected_claim}.bin`). For each prover:
`prepare` once; then per workload class `--warmup` untimed + `--runs` timed
rounds of the whole batch, one fresh `prove` process per request, sequential,
pinned to `--cpus` (the challenge hardware profile pins 8 vCPUs). Reported:
median batch wall time, per-request median, max peak RSS of `prove`,
proof bytes (min/max), median `verify` wall time and peak RSS
(`--verify-runs` per proof). Every claim is compared with expected_claim.bin
and every proof must verify (exit 0).
"""
import argparse, os, statistics, subprocess, sys, tempfile, time

ap = argparse.ArgumentParser()
ap.add_argument("--prover", action="append", required=True)
ap.add_argument("--params", required=True)
ap.add_argument("--cpus", default="0-7")
ap.add_argument("--warmup", type=int, default=1)
ap.add_argument("--runs", type=int, default=5)
ap.add_argument("--verify-runs", type=int, default=5)
ap.add_argument("--only-first", type=int, default=0, help="use only the first N cases per class")
ap.add_argument("workloads", nargs="+")
a = ap.parse_args()
tmp = tempfile.mkdtemp()


def timed(cmd):
    """Run under /usr/bin/time; return (exit, wall_s, peak_rss_kb)."""
    tf = os.path.join(tmp, "time")
    r = subprocess.run(["/usr/bin/time", "-f", "%e %M", "-o", tf, "taskset", "-c", a.cpus] + cmd,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    w, m = open(tf).read().split()[-2:]
    return r.returncode, float(w), int(m)


print("prover\tclass\trequests\tbatch_median_s\tbatch_min_s\tper_req_median_s\tprove_peak_rss_mb\t"
      "proof_bytes_min\tproof_bytes_max\tverify_median_ms\tverify_peak_rss_mb\tclaims_ok\tloadavg1")
for spec in a.prover:
    name, out = spec.split("=", 1)
    pub = os.path.join(tmp, name + "-public")
    subprocess.run([os.path.join(out, "prepare"), "--params", a.params, "--out", pub], check=True)
    for wl in a.workloads:
        cases = sorted(os.path.join(wl, "cases", c) for c in os.listdir(os.path.join(wl, "cases")))
        if a.only_first:
            cases = cases[: a.only_first]
        batches, per_req, rss, sizes, vts, vrss = [], [], [], [], [], []
        ok = True
        for rnd in range(a.warmup + a.runs):
            tot = 0.0
            for i, c in enumerate(cases):
                cl, pr = os.path.join(tmp, f"{name}-{i}.claim"), os.path.join(tmp, f"{name}-{i}.proof")
                t0 = time.perf_counter()
                code, w, m = timed([os.path.join(out, "prove"), "--public", pub, "--request", c + "/request.bin",
                                    "--witness", c + "/witness.bin", "--claim-out", cl, "--proof-out", pr])
                dt = time.perf_counter() - t0
                if code != 0:
                    sys.exit(f"{name}: prove failed on {c}")
                tot += w
                if rnd >= a.warmup:
                    per_req.append(w)
                    rss.append(m)
                if rnd == 0:
                    ok &= open(cl, "rb").read() == open(c + "/expected_claim.bin", "rb").read()
                    sizes.append(os.path.getsize(pr))
                    for _ in range(a.verify_runs):
                        vcode, vw, vm = timed([os.path.join(out, "verify"), "--public", pub, "--claim", cl,
                                               "--proof", pr])
                        if vcode != 0:
                            sys.exit(f"{name}: verify rejected honest proof of {c}")
                        vts.append(vw)
                        vrss.append(vm)
            if rnd >= a.warmup:
                batches.append(tot)
        load = open("/proc/loadavg").read().split()[0]
        print(f"{name}\t{os.path.basename(wl)}\t{len(cases)}\t{statistics.median(batches):.3f}\t{min(batches):.3f}\t"
              f"{statistics.median(per_req):.3f}\t{max(rss)//1024}\t{min(sizes)}\t{max(sizes)}\t"
              f"{statistics.median(vts)*1000:.0f}\t{max(vrss)//1024}\t{ok}\t{load}", flush=True)
