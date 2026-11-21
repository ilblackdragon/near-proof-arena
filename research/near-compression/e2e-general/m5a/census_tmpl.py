#!/usr/bin/env python3
"""B-T1: per-table heights of the template cut (`Tmpl.m5tIF` / `m5tSeg`) over the corpus, and the
template choice.

  census_tmpl.py run    --base DIR [--jobs 8] [--corpora d3c7,...] [--limit N] --out F.jsonl
  census_tmpl.py choose --in F.jsonl [--target 0.99] --out-dir TEMPLATES_DIR > summary.txt

`run`: for every corpus case, the Lean `allFeatures` run (`--emit-full`, the frozen checker binary
of the M5a-9 census), `extract_state.py` (main transition) and `tracegen.py --split --stats-only` at
the case's natural working-set depth D (one STATE segment for the whole transition): the natural
log height of every table of both templates (`SHA` and the `SHA512` chip included), the number of
SHA-512 compressions, the `HTAPE` rows (= `SREQ` + `HB` messages).  Cases that do not trace (the
completeness gaps of the M5a-9 census) are recorded with their outcome.

`choose`: nested template classes by working-set depth (each class pins D; a case with a smaller
natural D runs at the class's D: zero-padded leaves).  Heights that depend on D are moved to the
class D exactly: `WSB` 2^(D+1), `WSN` 2^(D+1) - 2 rows, `WSX` 24 - D rows; the IF chip gains
2 (2^D' - 2^D) - 3 (D' - D) compressions, a segment's `WSP` (D' - D) rows and its chip
2 (D' - D) - 3 (D' - D).  Within a class every other table's pin is the smallest height that keeps
the class's joint coverage at or above the target (a common per-table quantile).  A segment that
exceeds its template is cut into several STATE segments (cut-on-overflow); `choose` reports the
number of segments each case needs under the chosen seg template (greedy by write).

Run with `python3 -I`.
"""
import argparse
import json
import math
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
HEAVY = '/data/illia/nearproof-deps/bin/heavy'
LEAN = '/data/illia/nearproof-deps/m5a9/census/bin/nearspec-v3-check-successor'


def depth_for(n):
    return max(1, (max(n, 1) - 1).bit_length())


def lg(n):
    return max(2, (max(n, 4) - 1).bit_length())


def case_rec(base, case):
    wd = os.path.join(base, 'work', case.replace('/', '_'))
    os.makedirs(wd, exist_ok=True)
    rec = dict(corpus=case.rstrip('/').split('/')[-3], case=case.rstrip('/').split('/')[-1])
    full, st = os.path.join(wd, 'full.json'), os.path.join(wd, 'st.json')
    try:
        with open(full, 'w') as f:
            p = subprocess.run(['nice', '-n', '10', LEAN, '--tier', 'allFeatures', '--emit-full', case], stdout=f,
                               stderr=subprocess.PIPE, timeout=900)
        lean = json.loads(open(full).read().splitlines()[0])
        if lean['verdict'] != 'accept':
            rec['status'] = 'reject'
            return rec
        p = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'extract_state.py'), case, full, st],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900)
        if p.returncode:
            rec.update(status='error', error='extract:' + p.stderr.decode(errors='replace')[-200:])
            return rec
        s = json.load(open(st))
        if not s['changes']:
            rec['status'] = 'nochange'
            return rec
        keys = set(s['keys_read']) | set(k for k, _ in s['changes'])
        D = depth_for(len(keys))
        rec.update(status='state', keys=len(keys), changes=len(s['changes']), D=D)
        if D > 20:
            rec['gen'] = 'UNSUPPORTED:working set > 2^20'
            return rec
        names = os.path.join(base, 'air', 'if%d.names.json' % D)
        p = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'tracegen.py'), st, names, os.path.join(wd, 'x'),
                            '--split', '--stats-only'], stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=900)
        out = p.stdout.decode(errors='replace').strip().splitlines()
        if p.returncode == 0 and out:
            j = json.loads(out[-1])
            rec['gen'] = 'OK'
            rec['split'] = j['split']
            rec['writes'] = j['writes']
            # per-write STATE load (for cut-on-overflow): key + value bytes
            rec['wbytes'] = [len(k) // 2 + (0 if v is None else len(v) // 2) for k, v in s['changes']]
        else:
            err = p.stderr.decode(errors='replace').strip().splitlines()
            rec['gen'] = 'FAIL:' + (err[-1][:200] if err else 'rc=%d' % p.returncode)
    except Exception as e:  # noqa: BLE001
        rec.update(status='error', error='%s:%s' % (type(e).__name__, str(e)[:200]))
    finally:
        subprocess.run(['rm', '-rf', wd])
    return rec


def list_cases(corpora):
    out = []
    root = '/data/illia/nearproof-deps/corpora'
    for c in corpora:
        d = os.path.join(root, c, 'd3')
        for n in sorted(os.listdir(d)):
            if os.path.exists(os.path.join(d, n, 'claim.bin')):
                out.append(os.path.join(d, n))
    return out


def cmd_run(a):
    os.makedirs(os.path.join(a.base, 'air'), exist_ok=True)
    tool = os.path.join(HERE, 'lean', '.lake', 'build', 'bin', 'm5a-tool')
    for D in range(1, 13):
        f = os.path.join(a.base, 'air', 'if%d.names.json' % D)
        if not os.path.exists(f):
            subprocess.run([tool, 'tmpl-if', str(D), os.path.join(a.base, 'air', 'if%d.json' % D), f],
                           stdout=subprocess.DEVNULL, check=True)
    cases = list_cases(a.corpora.split(','))
    if a.limit:
        cases = cases[::max(1, len(cases) // a.limit)][:a.limit]
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            r = json.loads(line)
            done.add((r['corpus'], r['case']))
    todo = [c for c in cases if (c.split('/')[-3], c.split('/')[-1]) not in done]
    print('cases %d, todo %d' % (len(cases), len(todo)), flush=True)
    t0 = time.time()
    with open(a.out, 'a') as f, ThreadPoolExecutor(a.jobs) as ex:
        for i, r in enumerate(ex.map(lambda c: case_rec(a.base, c), todo)):
            f.write(json.dumps(r) + '\n')
            f.flush()
            if i % 200 == 0:
                print('%d/%d %.0fs' % (i, len(todo), time.time() - t0), flush=True)


# ------------------------------------------------------------------------------ choose
IF_FIXED_D = ('WSB', 'WSN', 'WSX')


def at_depth(r, D2):
    """The case's natural heights moved to the class depth D2 (exact for the D-dependent tables)."""
    D = r['D']
    s = r['split']
    hi = dict(s['if']['heights'])
    hi['WSB'] = D2 + 1
    hi['WSN'] = lg(2 ** (D2 + 1) - 2)
    hi['WSX'] = lg(24 - D2)
    ci = s['if']['compressions'] + 2 * (2 ** D2 - 2 ** D) - 3 * (D2 - D)
    hi['SHA512'] = lg(128 * ci)
    seg = s['seg0']
    hs = dict(seg['heights'])
    hs['WSP'] = lg(seg['rows']['WSP'] + (D2 - D))
    hs['WSX'] = lg(24 - D2)
    cs = seg['compressions'] - (D2 - D)
    hs['SHA512'] = lg(128 * cs)
    hs['HTAPE'] = lg(r['writes'] + sum(r['wbytes']))
    return hi, hs


def fits(h, pin):
    return all(h[t] <= pin[t] for t in pin)


def choose_pins(vecs, target):
    """Per-table pins: the smallest common quantile q whose per-table q-quantile pins keep the
    joint coverage of `vecs` at least `target`."""
    tables = sorted(vecs[0])
    cols = {t: sorted(v[t] for v in vecs) for t in tables}
    best = None
    for q in [x / 1000 for x in range(900, 1001)]:
        pin = {t: cols[t][min(len(vecs) - 1, math.ceil(q * len(vecs)) - 1)] for t in tables}
        cov = sum(1 for v in vecs if fits(v, pin)) / len(vecs)
        if cov >= target:
            best = (pin, cov, q)
            break
    if best is None:
        pin = {t: cols[t][-1] for t in tables}
        best = (pin, 1.0, 1.0)
    return best


def cells(pin, widths):
    return sum(widths.get(t, 0) << h for t, h in pin.items())


def cmd_choose(a):
    recs = [json.loads(line) for line in open(a.inp)]
    state = [r for r in recs if r.get('status') == 'state']
    ok = [r for r in state if r.get('gen') == 'OK']
    print('cases %d, state %d, trace OK %d (%.2f %%)' % (len(recs), len(state), len(ok), 100 * len(ok) / max(1, len(state))))
    byD = {}
    for r in ok:
        byD[r['D']] = byD.get(r['D'], 0) + 1
    print('natural D:', dict(sorted(byD.items())))
    classes = [int(x) for x in a.classes.split(',')]
    left = list(ok)
    out = []
    os.makedirs(a.out_dir, exist_ok=True)
    for i, D2 in enumerate(classes):
        mem = [r for r in left if r['D'] <= D2]
        if not mem:
            continue
        vi, vs = zip(*[at_depth(r, D2) for r in mem])
        pin_i, cov_i, qi = choose_pins(list(vi), a.target)
        # the segment template: covers the class's single-segment cases at the target; the rest are
        # cut into several segments (cut-on-overflow)
        pin_s, cov_s, qs = choose_pins(list(vs), a.target)
        fit = [r for r, h in zip(mem, vi) if fits(h, pin_i)]
        name = 'SML'[i] if i < 3 else 'C%d' % i
        print('\nclass %s: D = %d, members %d (natural D <= %d not in an earlier class), IF covers %d (%.2f %%, q %.3f); '
              'one-segment seg covers %.2f %% (q %.3f)' % (name, D2, len(mem), D2, len(fit), 100 * cov_i, qi, 100 * cov_s, qs))
        print('  IF  pins', json.dumps(pin_i))
        print('  seg pins', json.dumps(pin_s))
        # segments needed (greedy by write, STB rows ~ bytes): the seg pins bound the bytes per segment
        cap = (1 << pin_s['STB'])
        nseg = []
        for r in fit:
            n, acc = 1, 0
            for b in r['wbytes']:
                if acc + b > cap:
                    n, acc = n + 1, 0
                acc += b
            nseg.append(n)
        hist = {}
        for n in nseg:
            hist[n] = hist.get(n, 0) + 1
        print('  STATE segments per case (cut on STB overflow):', dict(sorted(hist.items())))
        out.append(dict(name=name, D=D2, members=len(mem), covered=len(fit), pin_if=pin_i, pin_seg=pin_s))
        left = [r for r in left if r not in fit]
    tot = sum(c['covered'] for c in out)
    print('\ntotal covered %d / %d trace-OK cases (%.2f %%); of all state cases %.2f %%'
          % (tot, len(ok), 100 * tot / max(1, len(ok)), 100 * tot / max(1, len(state))))
    json.dump(out, open(os.path.join(a.out_dir, 'classes.json'), 'w'), indent=1)


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('run')
    r.add_argument('--base', required=True)
    r.add_argument('--jobs', type=int, default=8)
    r.add_argument('--corpora', default='d3c7,d3c8,d3c9,d3c10')
    r.add_argument('--limit', type=int, default=0)
    r.add_argument('--out', required=True)
    c = sp.add_parser('choose')
    c.add_argument('--in', dest='inp', required=True)
    c.add_argument('--target', type=float, default=0.99)
    c.add_argument('--classes', default='5,7')
    c.add_argument('--out-dir', required=True)
    a = ap.parse_args()
    {'run': cmd_run, 'choose': cmd_choose}[a.cmd](a)


if __name__ == '__main__':
    main()
