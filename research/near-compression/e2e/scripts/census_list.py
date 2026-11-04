import json, os
roots = {'d1': '/data/illia/nearproof-deps/corpora/d1run/d1', 'd2': '/data/illia/nearproof-deps/corpora/d2corpus.v2/d2'}
for c in ['d3c7', 'd3c8', 'd3c9', 'd3c10']:
    roots[c] = f'/data/illia/nearproof-deps/corpora/{c}/d3'
for k, r in roots.items():
    for n in sorted(os.listdir(r)):
        try:
            m = json.load(open(f'{r}/{n}/meta.json'))
        except Exception:
            continue
        if m.get('kind') == 'honest' and m.get('expected_rel_d0') and m.get('in_d0'):
            print(f'{k} {r}/{n}')
