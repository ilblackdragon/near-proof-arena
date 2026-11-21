"""E2E-D D-9: one line per tree run (RESULT.json + verify logs + prove.log peak RSS):
chunk, class, family, packet bytes, total prove s (and without setup-only probes), per-proof s,
verify ms (min-max over the 3 fresh processes), peak GB.
usage: summary_d9.py RUN_DIR...
"""
import json, pathlib, re, sys

for d in map(pathlib.Path, sys.argv[1:]):
    r = json.loads((d / 'RESULT.json').read_text())
    s = r['seconds']
    probe = sum(v for k, v in s.items() if 'probe' in k)
    leaves = [round(s[k]) for k in sorted(s) if k.startswith('leaf')]
    vms = []
    for v in sorted(d.glob('verify*.log')):
        m = re.search(r'VERIFY_PROFILE_MS total=([0-9.]+) wrap_verify=([0-9.]+)', v.read_text())
        if m:
            vms.append((float(m.group(1)), float(m.group(2))))
    rss = re.findall(r'Maximum resident set size \(kbytes\): (\d+)', (d / 'prove.log').read_text())
    peak = int(rss[-1]) / 1e6 if rss else float('nan')
    ident = 'TREE_FIXED_SETUP_IDENTICAL' in (d / 'prove.log').read_text()
    print(f"{d.name} class={r['class']} family={r.get('family')} packet={r['bundle_bytes']} prove_s={r['total_seconds']:.0f} "
          f"prove_s_wo_probe={r['total_seconds'] - probe:.0f} leaves={leaves} P2={s.get('node2_0', 0):.0f} wrap={s['wrap']:.0f} "
          f"verify_ms={min(x[0] for x in vms):.1f}-{max(x[0] for x in vms):.1f} wrap_verify_ms={min(x[1] for x in vms):.1f}-{max(x[1] for x in vms):.1f} "
          f"peak_GB={peak:.1f} zk={r['zero_knowledge_established']} fixed_setup_identical={ident}")
