import subprocess, json, collections
from concurrent.futures import ThreadPoolExecutor
S = '/data/illia/nearproof-deps/w12-o4b'
cases = open(f'{S}/ho/shard13.txt').read().split()
bs = [cases[i:i + 25] for i in range(0, len(cases), 25)]


def run(binary):
    def one(b):
        return subprocess.run([f'{S}/{binary}', '--tier', 'signed', *b], capture_output=True, text=True).stdout
    with ThreadPoolExecutor(5) as ex:
        out = ''.join(ex.map(one, bs))
    open(f'{S}/ho/s13-{binary}.jsonl', 'w').write(out)
    return {json.loads(l)['case']: json.loads(l) for l in out.splitlines()}


b, a = run('check-before'), run('check-after')
print('s13', len(b), len(a), dict(collections.Counter(x['verdict'] for x in a.values())),
      'before', dict(collections.Counter(x['verdict'] for x in b.values())),
      'changed', sum((b[k]['verdict'], b[k]['reason']) != (a[k]['verdict'], a[k]['reason']) for k in a))
