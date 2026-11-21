#!/usr/bin/env python3
"""G-2: a height census of the FINAL (class F1) and INIT templates over a corpus.

    census.py run CORPUS_DIR OUT.jsonl [--sample N] [--seed S] [--jobs J] [--only final|init]
    census.py summary OUT.jsonl…

`run`: for every case (or a seeded random sample of N), the Lean checker's dump (`m5d-tool dump`),
then `tracegen.py`'s natural heights (`Gen.natural`: the `fit` log heights a template pin must
cover, every Lean table with one padding row, `SHA` and the chip `SHA512` included) for both
templates, one JSON line per case. The AIR names are exported once (`m5d-tool air-final|air-init`).
A case the FINAL generator does not take (not class F1) is recorded with its error.
`summary`: per table the max and the 99 / 99.9 % quantiles of the fit heights, and the joint
coverage of the shipped templates (`templates/*.json`).
Box rules: ≤ 8 jobs; temp dumps under /data/illia/nearproof-deps/e2e-m5d/census (deleted per case).
"""
import json
import os
import random
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tracegen  # noqa: E402

TOOL = os.path.join(HERE, 'lean/.lake/build/bin/m5d-tool')
TMP = '/data/illia/nearproof-deps/e2e-m5d/census'
NAMES = {}


def one(arg):
    case, kinds = arg
    rec = dict(case=os.path.basename(case))
    fd, path = tempfile.mkstemp(suffix='.json', dir=TMP)
    os.close(fd)
    try:
        r = subprocess.run([TOOL, 'dump', case, path], capture_output=True, text=True, timeout=300)
        if r.returncode != 0:
            rec['dump'] = (r.stdout + r.stderr).strip().splitlines()[-1:] or ['exit %d' % r.returncode]
            return rec
        d = json.load(open(path))
        for t in kinds:
            G = tracegen.GenInit if t == 'init' else tracegen.Gen
            try:
                g = G(d, NAMES[t])
                info = g.run()
                rec[t] = dict(fit=g.natural()[1], info={k: v for k, v in info.items() if isinstance(v, int)},
                              comps=len(g.comps), sha_msgs=len(g.sha_msgs))
            except Exception as e:  # noqa: BLE001 (a case outside the class)
                rec[t] = dict(error='%s: %s' % (type(e).__name__, str(e)[:200]))
    finally:
        os.unlink(path)
    return rec


def init_names(nm):
    NAMES.update(nm)


def cmd_run(corpus, out, sample=None, seed=1, jobs=8, kinds=('final', 'init')):
    os.makedirs(TMP, exist_ok=True)
    nm = {}
    for t in ('final', 'init'):
        a, n = os.path.join(TMP, t + '.json'), os.path.join(TMP, t + '-names.json')
        subprocess.run([TOOL, 'air-' + t, a, n], check=True, capture_output=True)
        nm[t] = json.load(open(n))
    cases = sorted(os.path.join(corpus, c) for c in os.listdir(corpus))
    if sample:
        cases = sorted(random.Random(seed).sample(cases, min(sample, len(cases))))
    with open(out, 'w') as f, ProcessPoolExecutor(jobs, initializer=init_names, initargs=(nm,)) as ex:
        for i, rec in enumerate(ex.map(one, [(c, kinds) for c in cases], chunksize=4)):
            f.write(json.dumps(rec) + '\n')
            if i % 200 == 0:
                print(i, rec['case'], file=sys.stderr)


def quant(xs, q):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(q * len(xs)))]


def cmd_summary(*paths):
    recs = [json.loads(line) for path in paths for line in open(path)]
    print('cases %d, dump OK %d' % (len(recs), sum('dump' not in r for r in recs)))
    tmpls = {}
    tdir = os.path.join(HERE, 'templates')
    for fn in sorted(os.listdir(tdir)) if os.path.isdir(tdir) else []:
        t = json.load(open(os.path.join(tdir, fn)))
        tmpls.setdefault(t['template'], []).append(t)
    for t in ('final', 'init'):
        ok = [r[t] for r in recs if t in r and 'fit' in r[t]]
        errs = {}
        for r in recs:
            if t in r and 'error' in r[t]:
                k = r[t]['error'][:60]
                errs[k] = errs.get(k, 0) + 1
        print('\n%s: %d cases in the class; outside: %s' % (t.upper(), len(ok), dict(sorted(errs.items(), key=lambda x: -x[1])[:5])))
        if not ok:
            continue
        for tb in ok[0]['fit']:
            hs = [r['fit'][tb] for r in ok]
            print('  %-7s min %2d  q99 %2d  q99.9 %2d  max %2d' % (tb, min(hs), quant(hs, .99), quant(hs, .999), max(hs)))
        for k in ok[0]['info']:
            vs = [r['info'][k] for r in ok]
            print('  info %-9s min %6d  q99 %6d  max %6d' % (k, min(vs), quant(vs, .99), max(vs)))
        left = list(ok)
        for tm in sorted(tmpls.get(t, []), key=lambda x: sum(x['heights'].values())):
            fits = [r for r in left if all(r['fit'][k] <= tm['heights'][k] for k in r['fit'])]
            print('  template %-8s covers %d / %d of the class (%.2f %%), %d of those not covered by a smaller one'
                  % (tm['name'], sum(all(r['fit'][k] <= tm['heights'][k] for k in r['fit']) for r in ok), len(ok),
                     100 * sum(all(r['fit'][k] <= tm['heights'][k] for k in r['fit']) for r in ok) / len(ok), len(fits)))
            left = [r for r in left if r not in fits]
        if tmpls.get(t):
            print('  left by every template: %d' % len(left))


SHA_W, CHIP_W, CHIPT_CELLS = 544, 83, 9 * 128   # sha256gen::WIDTH, s384::air::{WIDTH, T_WIDTH·ROWS}


def widths(kind):
    n = os.path.join(TMP, kind + '-names.json')
    if not os.path.exists(n):
        os.makedirs(TMP, exist_ok=True)
        subprocess.run([TOOL, 'air-' + kind, os.path.join(TMP, kind + '.json'), n], check=True, capture_output=True)
    nm = json.load(open(n))
    w = {t: len(nm['cols'][t]) for t in nm['tables'] if t != 'SHA'}
    if 'SHA' in nm['tables']:
        w['SHA'] = SHA_W
    w['SHA512'] = CHIP_W
    return w


def cmd_mktmpl(name, kind, n_stack, pins, note=''):
    """A template file: the pins (every table of the export + `SHA512`) and lane D's base
    configuration at `n_stack`, lb 1, grinding 24; `w_stack` = the stacked width of the pinned
    shape + 2 (packing slack), as lane B's `census_tmpl.py::params`."""
    w = widths(kind)
    assert set(pins) == set(w), ('pins must cover exactly', sorted(w), sorted(pins))
    col = 1 << (n_stack + 2)
    assert max(pins.values()) <= n_stack + 2, 'a table taller than a stacked column'
    cells = sum(w[t] << h for t, h in pins.items()) + CHIPT_CELLS
    t = dict(name=name, template=kind, note=note,
             params=dict(n_stack=n_stack, log_blowup=1, w_stack=-(-cells // col) + 2, pow_bits=24, degree=9),
             heights=dict(sorted(pins.items())), cells=cells)
    os.makedirs(os.path.join(HERE, 'templates'), exist_ok=True)
    json.dump(t, open(os.path.join(HERE, 'templates', name + '.json'), 'w'), indent=1)
    print('template %s (%s): %.2f M cells, n_stack %d, w_stack %d' % (name, kind, cells / 1e6, n_stack, t['params']['w_stack']))


def main():
    a = sys.argv[1:]
    opt = lambda k, d: type(d)(a[a.index(k) + 1]) if k in a else d
    if a[0] == 'run':
        cmd_run(a[1], a[2], opt('--sample', 0) or None, opt('--seed', 1), opt('--jobs', 8),
                tuple(opt('--only', 'final,init').split(',')))
    elif a[0] == 'mktmpl':
        # census.py mktmpl NAME final|init N_STACK TABLE=LOG … [--note TEXT]
        note = opt('--note', '')
        rest = [x for i, x in enumerate(a) if i >= 4 and '=' in x and a[i - 1] != '--note']
        cmd_mktmpl(a[1], a[2], int(a[3]), {k: int(v) for k, v in (x.split('=') for x in rest)}, note)
    else:
        cmd_summary(*a[1:])


if __name__ == '__main__':
    main()
