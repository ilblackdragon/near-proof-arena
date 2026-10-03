#!/usr/bin/env bash
# Measure microVM run latency: N sequential `/bin/true` runs (+ optional
# parallelism P). Prints p50/p95/max of each phase in milliseconds.
#   usage: latency.sh [N=30] [P=1]
set -euo pipefail
N=${1:-30}; P=${2:-1}
repo=$(cd "$(dirname "$0")/../../.." && pwd)
cd "$repo"
cargo build -q --release -p arena-firecracker --bin arena-fc-run
bin="$repo/target/release/arena-fc-run"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
seq "$N" | xargs -P "$P" -I{} sh -c "'$bin' --mem-mb 256 --scratch-mb 64 -- /bin/true > '$tmp/{}.json'"
python3 - "$tmp" "$N" "$P" <<'PY'
import json, os, sys
d, n, p = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rows = [json.load(open(os.path.join(d, f))) for f in os.listdir(d)]
def q(xs, f):
    xs = sorted(xs); return xs[min(len(xs) - 1, int(f * len(xs)))]
cols = {
    "boot (jailer spawn -> guest start marker)": [r["diagnostics"]["boot_ns"] for r in rows],
    "candidate wall (/bin/true)": [r["wall_ns"] for r in rows],
    "teardown (exit marker -> VMM exit)": [r["diagnostics"]["teardown_ns"] for r in rows],
    "VMM lifetime": [r["diagnostics"]["vmm_wall_ns"] for r in rows],
    "end-to-end (docker run -> exit)": [r["diagnostics"]["total_ns"] for r in rows],
    "host cgroup cpu": [r["cpu_ns"] for r in rows],
}
print(f"runs={len(rows)} parallel={p}")
for k, v in cols.items():
    print(f"{k:45s} p50={q(v,.5)/1e6:8.1f}ms p95={q(v,.95)/1e6:8.1f}ms max={max(v)/1e6:8.1f}ms")
print(f"{'host cgroup memory.peak':45s} p50={q([r['peak_rss_bytes'] for r in rows],.5)/2**20:8.1f}MiB")
PY
