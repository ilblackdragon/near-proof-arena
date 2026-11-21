import json, sys, collections
rows = [json.loads(l) for l in open(sys.argv[1])]
segs = [s for r in rows for s in r['segs']]
c = collections.Counter()
for s in segs:
    if s['pre']:
        c['pre_ok'] += 1
    elif 'fail' in s:
        f = s['fail']
        c['fail_bus214' if '214' in f.split('first')[0] else 'fail_other'] += 1
    else:
        c['no_precheck_line'] += 1
print('calls', len(rows), 'calls_ok', sum(r['ok'] for r in rows), 'buildfail', sum(1 for r in rows if r['buildfail']),
      'segments', len(segs), dict(c))
other = collections.Counter(s['fail'][:60] for s in segs if not s['pre'] and 'fail' in s and '214' not in s['fail'].split('first')[0])
for k, v in other.most_common(10):
    print(v, k)
