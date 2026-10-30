import collections, glob, json, sys
c = collections.Counter()
for root in sys.argv[1:]:
    for p in glob.glob(root + '/*/*/meta.json'):
        m = json.load(open(p))
        v = m.get('d3_violations') or []
        code = [x for x in v if x.startswith('e.code')]
        pr = m.get('nearcore_probe') or {}
        sch = m.get('nearcore_schedule')
        key = (m['kind'], tuple(code), 'cold_ok' if m['nearcore'] == 'ok' else 'cold_err',
               'warm_ok' if pr.get('warm') == 'ok' else ('warm_err' if pr else '-'),
               'pois_ok' if pr.get('poisoned') == 'ok' else ('pois_err' if pr else '-'),
               ('sched', sch['eager'] == 'ok', sch['lazy'] == 'ok') if sch else '')
        c[key] += 1
for k, n in sorted(c.items(), key=lambda kv: -kv[1]):
    print(n, k)
