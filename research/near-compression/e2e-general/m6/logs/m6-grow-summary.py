import json, collections, re, sys
rows = [json.loads(l) for l in open(sys.argv[1] if len(sys.argv) > 1 else '/data/illia/nearproof-deps/e2e-laneA/m6-grow/segcheck.jsonl')]
cls = collections.Counter()
hids = collections.Counter()
other = collections.Counter()
for r in rows:
    if r.get('buildfail'):
        cls['build: ' + r['buildfail'].split(':', 1)[1].strip()[:80]] += 1
    for s in r['segs']:
        if s['pre']:
            continue
        f = s.get('fail', '?')
        m = re.search(r'by bus \{([^}]*)\}', f)
        if m:
            buses = m[1]
            cls['precheck buses ' + re.sub(r': \d+', '', buses)] += 1
            for h in re.findall(r'\(\(214, \[\d+, (\d+)\]\)', f):
                hids[int(h)] += 1
        else:
            other[f[:120]] += 1
print(dict(cls))
print('hid keys on 214', dict(hids))
print('other', dict(other))
# calls fully OK, calls whose every grow segment is OK
gseg = [(r, s) for r in rows for s in r['segs'] if s.get('grow', 0) + s.get('size', 0) > 0]
print('grow segs', len(gseg), 'ok', sum(s['pre'] for _, s in gseg))
# grow calls whose grow seg not built (build fail before it)
nobuilt = [r for r in rows if not any(s.get('grow', 0) for s in r['segs'])]
print('calls with no built grow segment', len(nobuilt), collections.Counter(bool(r.get('buildfail')) for r in nobuilt))
