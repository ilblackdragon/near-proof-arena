"""Peak RSS (max of verifier and its statepublic child) and wall of one fresh-process verify, 1 thread.
usage: verify_rss.py RUN_DIR CASE_DIR"""
import os, pathlib, resource, subprocess, sys, time
run, case = map(pathlib.Path, sys.argv[1:3])
root = pathlib.Path(__file__).resolve().parents[4]
d = pathlib.Path('/data/illia/nearproof-deps/pq-e2e-zk')
t = time.time()
r = subprocess.run(['taskset', '-c', '15', str(d / 'target/release/nearproof-chunk-e2e'), 'verify',
                    str(root / 'examples/np-udr-stark-v2/source/near-air-v3.json'), str(case / 'claim.bin'),
                    str(d / 'target-classical/release/examples/statepublic'), str(run / 'SETUP.json'),
                    (run / 'SETUP.sha256').read_text().strip(), str(run / 'FINAL.bundle')],
                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT, env=dict(os.environ, RAYON_NUM_THREADS='1'))
w = time.time() - t
print(run.name, 'ok' if r.returncode == 0 else 'FAIL', 'wall_ms=%.1f' % (w * 1e3),
      'max_child_rss_mb=%.1f' % (resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024))
