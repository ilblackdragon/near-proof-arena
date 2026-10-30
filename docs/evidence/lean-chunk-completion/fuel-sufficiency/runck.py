import subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor
binary, cases_file, out, tier = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 3
cases = [l.strip() for l in open(cases_file) if l.strip()]
batches = [cases[i:i + 40] for i in range(0, len(cases), 40)]
def run(b):
    try:
        r = subprocess.run([binary, "--tier", tier] + b, capture_output=True, text=True, timeout=7200)
        return r.stdout
    except subprocess.TimeoutExpired:
        return "".join(f'{{"case":"{c}","verdict":"TIMEOUT"}}\n' for c in b)
with ThreadPoolExecutor(jobs) as ex, open(out, "w") as f:
    for s in ex.map(run, batches):
        f.write(s)
print("done", len(cases))
