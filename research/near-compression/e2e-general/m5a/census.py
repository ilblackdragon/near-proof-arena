#!/usr/bin/env python3
"""M5a-9 corpus coverage census of the state circuit (M5b AIR, `m5a-tool airb D`).

For every corpus case: the Lean `allFeatures` run (`--emit-full`), the clean-room state extraction
(`extract_state.py`, main transition = the circuit's scope; every other transition with changes is
traced separately), `tracegen.py` on an M5b export of the smallest working-set depth D with
2^D >= |working set| (1 <= D <= 20), and the prover's `check` mode (every constraint on every row,
every bus balanced) on each trace that generates.  Dumps are deleted after the check.

  census.py run   --base DIR [--jobs 8] [--limit N] [--corpora d3c7,d3c8,...] [--out F.jsonl]
  census.py case  --base DIR CASE WORKDIR          (one case; prints one JSON record; internal)
  census.py prove --base DIR --in F.jsonl --n 15 --out F.prove.jsonl   (full prove on a sample)
  census.py summary --in F.jsonl [--prove F.prove.jsonl] > summary.txt
  census.py compact --in F.jsonl --out logs/M5a9-census.jsonl     (the repo's per-case log)

--base DIR is the isolated census root, holding
  tools/   copies of tracegen.py, ptrie.py, sha512c.py and extract_state.py (the census copy:
           ROOT -> base/oracle_root, `extract()` returns every transition, `--all` mode)
  oracle_root/oracle/{tools,wasm-d3/cleanroom}   the clean-room checker the extraction imports
  bin/     nearspec-v3-check-successor, m5a-tool, nearproof-e2e-m5a (copied, so rebuilds elsewhere
           do not affect a run)
  air/     m5b{D}.json, names{D}.json for D = 1..20 (`m5a-tool airb D`)
  work/    per-case temp dirs (deleted)

Extraction fix (census copy of extract_state.py): witness nodes first read during finalize (e.g. a
squash sibling the find walks never touched) are recorded too (`fin_nodes_read`); the repo's tool
drops them, so tracegen saw an unrevealed sibling.  `gen_orig` is the outcome without them.

Record fields (one JSON line per case): corpus, case, status (reject | nochange | state | error),
verdict, n_trans, keys (working-set size), changes, D, gen (OK | UNSUPPORTED:<shape> | ERROR:<..>),
gen_raw (raw first-failure message), check (OK | FAIL:<msg> | ERROR), stb / stw / rows / heights,
cells, htape_h, gaps (every distinct Unsupported shape a fault-tolerant first pass meets, with
counts; `find|`/`upsert|`/`delete|` prefixes), spec_ops (`ptrie.apply_changes` path cases),
implicit (per implicit transition: keys, changes, gen, stb).

Caveat: the `gaps` probe is the unbatched first pass (no version plan), so the plan-only shape
'final node over an in-memory child (continued key)' shows up only as the first failure.
Run with `python3 -I`.
"""
import argparse
import collections
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
from concurrent.futures import ThreadPoolExecutor

HEAVY = '/data/illia/nearproof-deps/bin/heavy'


def paths(base):
    return dict(tools=os.path.join(base, 'tools'), bin=os.path.join(base, 'bin'),
                air=os.path.join(base, 'air'), work=os.path.join(base, 'work'),
                lean=os.path.join(base, 'bin', 'nearspec-v3-check-successor'),
                prover=os.path.join(base, 'bin', 'nearproof-e2e-m5a'))


def depth_for(n):
    return max(1, (max(n, 1) - 1).bit_length())


# ------------------------------------------------------------------------------ one case
RKN = {0: 'ANS', 1: 'H', 2: 'HB', 3: 'HE', 4: 'LD', 5: 'NONE', 6: 'SAME'}


def norm(msg, KMAX=64):
    m = re.match(r'mismatch at nibble (\d+) of a (\d+)-nibble node key', msg)
    if m:
        jm, L = int(m.group(1)), int(m.group(2))
        return 'mismatch past the head of a continued node key' if L > KMAX else \
            'mismatch at the end of a %d-nibble node key' % L
    m = re.match(r'delete under an extension with a (\d+) child result', msg)
    if m:
        return 'delete under an extension with a %s child result' % RKN.get(int(m.group(1)), m.group(1))
    m = re.match(r'root result (\d+)', msg)
    if m:
        return 'root result %s' % RKN.get(int(m.group(1)), m.group(1))
    return re.sub(r'\d+', 'N', msg)


def exc_label(e):
    s = str(e).strip().splitlines()
    return '%s:%s' % (type(e).__name__, s[0][:120] if s else '')


def gen_trace(TG, PT, st, names, out):
    """tracegen.main without mutants: pass 1 (unbatched) -> plan -> pass 2 (batched), write."""
    g = TG.make_gen(st, names, None, None, 1, 0)
    plan = g.make_plan()
    PT.OVERRIDE.clear()
    g = TG.make_gen(st, names, None, plan, 1, 0)
    return g.write(out)


def probe_gaps(TG, PT, st, names):
    """Fault-tolerant first pass: every find / change walk run separately; an Unsupported walk is
    recorded and the spec's applyChange result taken instead, so later changes still run."""
    import hashlib
    gaps = collections.Counter()
    g = TG.Gen(st, names, None, None, 1, 0)
    st_pre = PT.reveal_all(g.store, g.pre_root)
    for i, key in enumerate(g.keys):
        ctx = dict(w=i, kid=i, mode=0, K=PT.nibbles(key), vlen=0, vh=bytes(32))
        try:
            g.walk(st_pre, 0, ctx)
        except TG.Unsupported as e:
            gaps['find|' + norm(str(e))] += 1
    chg = dict(g.changes)
    cur = st_pre
    for i, key in enumerate(g.keys):
        if key not in chg:
            continue
        v = chg[key]
        ref = (1, len(v), hashlib.sha256(v).digest()) if v is not None else (0, 0, bytes(32))
        ctx = dict(w=TG.W_FINAL + i, kid=i, mode=1 if v is not None else 2, K=PT.nibbles(key),
                   vlen=ref[1], vh=ref[2])
        try:
            res = g.walk(cur, 0, ctx)
            if res['rk'] not in (TG.RK_H, TG.RK_HB, TG.RK_HE, TG.RK_SAME):
                raise TG.Unsupported('root result %d' % res['rk'])
            cur = res['node']
        except TG.Unsupported as e:
            gaps[('upsert|' if v is not None else 'delete|') + norm(str(e))] += 1
            r = PT.apply_change(cur, key, None if v is None else (ref[1], ref[2]), [])
            if r[0] != 'ok':
                raise RuntimeError('spec applyChange missing')
            cur = r[1]
    return dict(gaps)


def spec_ops(PT, st):
    import hashlib
    store = {hashlib.sha256(bytes.fromhex(n)).digest(): bytes.fromhex(n) for n in st['nodes_read']}
    t = PT.reveal_all(store, bytes.fromhex(st['pre_root']))
    if t == ('hash', bytes(32)):
        t = None
    ch = [(bytes.fromhex(k), None if v is None else (len(bytes.fromhex(v)), hashlib.sha256(bytes.fromhex(v)).digest()))
          for k, v in st['changes']]
    _, allops = PT.apply_changes(t, ch)
    c = collections.Counter()
    for ops in allops:
        for o in ops:
            c[o] += 1
    return dict(c)


def trace_one(TG, PT, P, st, out, rec, with_probe=True):
    keys = set(st['keys_read']) | set(k for k, _ in st['changes'])
    n = len(keys)
    D = depth_for(n)
    rec.update(keys=n, changes=len(st['changes']), D=D,
               nodes=len(st['nodes_read']),
               deletes=sum(1 for _, v in st['changes'] if v is None),
               maxkey=max((len(k) // 2 for k in keys), default=0),
               maxval=max((len(v) // 2 for _, v in st['changes'] if v is not None), default=0))
    if D > 20:
        rec['gen'] = 'UNSUPPORTED:working set > 2^20'
        return False
    names = json.load(open(os.path.join(P['air'], 'names%d.json' % D)))
    try:
        rec['spec_ops'] = spec_ops(PT, st)
    except Exception as e:  # noqa: BLE001
        rec['spec_ops_error'] = exc_label(e)
    ok = False
    try:
        stats = gen_trace(TG, PT, st, names, out)
        rec['gen'] = 'OK'
        rows = stats['rows']
        rec['stb'], rec['stw'] = rows.get('STB'), rows.get('STW')
        rec['rows'] = rows
        rec['heights'] = {k: v.bit_length() - 1 for k, v in stats['heights'].items()}
        rec['sha_blocks'], rec['comps'] = stats.get('sha_blocks'), stats.get('compressions')
        rec['post_root'] = stats.get('post_root')
        ok = True
    except TG.Unsupported as e:
        rec['gen'] = 'UNSUPPORTED:' + norm(str(e))
        rec['gen_raw'] = str(e)
    except AssertionError as e:
        a0 = e.args[0] if e.args else None
        if isinstance(a0, tuple) and a0 and a0[0] == 'version readers':
            rec['gen'] = 'ERROR:version readers >= 2^%d (VBITS)' % TG.VBITS
            rec['gen_raw'] = str(a0)
        else:
            rec['gen'] = 'ERROR:' + exc_label(e)
            rec['gen_tb'] = traceback.format_exc()[-1500:]
    except Exception as e:  # noqa: BLE001
        rec['gen'] = 'ERROR:' + exc_label(e)
        rec['gen_tb'] = traceback.format_exc()[-1500:]
    PT.OVERRIDE.clear()
    if with_probe:
        try:
            rec['gaps'] = probe_gaps(TG, PT, st, names)
        except Exception as e:  # noqa: BLE001
            rec['probe_error'] = exc_label(e)
    return ok


def refine_split(TG, PT):
    """Census-only: name which key ends at the new branch in tracegen's 'split where a key ends
    at the branch' (the old node's key -> splitLeaf.oldEnds; the written key -> splitLeaf.newEnds /
    splitExt.newEnds)."""
    orig = TG.Gen.split

    def split(self, t, d, ctx):
        try:
            return orig(self, t, d, ctx)
        except TG.Unsupported as e:
            if str(e) != 'split where a key ends at the branch':
                raise
            k, rest = t[1], ctx['K'][d:]
            jm = len(PT.common_prefix(k, rest))
            side = 'both keys end' if jm >= len(k) and jm >= len(rest) else \
                'old %s key ends' % t[0] if jm >= len(k) else 'written key ends inside a %s' % t[0]
            raise TG.Unsupported('split where a key ends at the branch (%s)' % side)
    TG.Gen.split = split


def do_case(base, case, wd):
    P = paths(base)
    sys.path.insert(0, P['tools'])
    sys.setrecursionlimit(100000)
    import extract_state as ES
    import ptrie as PT
    import tracegen as TG
    refine_split(TG, PT)
    rec = dict(corpus=case.rstrip('/').split('/')[-3], case=case.rstrip('/').split('/')[-1])
    os.makedirs(wd, exist_ok=True)
    full = os.path.join(wd, 'full.json')
    with open(full, 'w') as f:
        p = subprocess.run([P['lean'], '--tier', 'allFeatures', '--emit-full', case], stdout=f,
                           stderr=subprocess.PIPE, timeout=600)
    try:
        lean = json.loads(open(full).read().splitlines()[0])
        rec['verdict'] = lean['verdict']
    except Exception as e:  # noqa: BLE001
        rec.update(status='error', error='lean:' + exc_label(e), lean_rc=p.returncode,
                   lean_err=p.stderr.decode(errors='replace')[-300:])
        return rec
    if lean['verdict'] != 'accept':
        rec['status'] = 'reject'
        return rec
    try:
        res, allt = ES.extract(case, full)
    except Exception as e:  # noqa: BLE001
        rec.update(status='error', error='extract:' + exc_label(e))
        return rec
    rec['n_trans'] = res['n_transitions']
    rec['clean_room'] = res['clean_room_verdict']
    rec['lean_match'] = res['lean_matches_clean_room']
    rec['post_eq_header'] = res['post_root'] == res['header_state_root']
    # implicit transitions (everything after the main one) with changes: traced, not checked
    imp = []
    for t in allt:
        if t['transition'] == 0 or not t['changes']:
            continue
        r2 = dict(t=t['transition'], fin_nodes=len(t.get('fin_nodes_read', [])))
        od = os.path.join(wd, 'imp')
        t = dict(t, nodes_read=t['nodes_read'] + t.get('fin_nodes_read', []))
        trace_one(TG, PT, P, t, od, r2, with_probe=False)
        shutil.rmtree(od, ignore_errors=True)
        for k in ('rows', 'heights', 'spec_ops', 'gen_tb', 'post_root'):
            r2.pop(k, None)
        imp.append(r2)
    if imp:
        rec['implicit'] = imp
    rec['implicit_with_changes'] = len(imp)
    if not res['changes']:
        rec['status'] = 'nochange'
        return rec
    rec['status'] = 'state'
    rec['fin_nodes'] = len(res.get('fin_nodes_read', []))
    if rec['fin_nodes']:
        # as the repo's extract_state.py at 61d19af1f (nodes first read during finalize omitted)
        r0 = {}
        trace_one(TG, PT, P, res, os.path.join(wd, 'orig'), r0, with_probe=False)
        shutil.rmtree(os.path.join(wd, 'orig'), ignore_errors=True)
        rec['gen_orig'] = r0.get('gen')
    st = dict(res, nodes_read=res['nodes_read'] + res.get('fin_nodes_read', []))
    ok = trace_one(TG, PT, P, st, os.path.join(wd, 'dump'), rec)
    if ok and rec.get('post_root') not in (None, res['post_root']):
        rec['gen'] = 'ERROR:post_root mismatch vs extraction'
        ok = False
    rec['dump'] = os.path.join(wd, 'dump') if ok else None
    return rec


# ------------------------------------------------------------------------------ prover
PROVER_LOCK = threading.Lock()
CHECK_SEM = threading.Semaphore(8)


def run_prover(P, D, dump, mode, threads=8, mem='32G', timeout=3600):
    """`prove`: one at a time, 8 threads.  `check` (load + precheck: single-threaded, ~50 MB):
    RAYON_NUM_THREADS=1, inside the worker-process cap (`--check-par`)."""
    cmd = ['env', 'HEAVY_MEM=%s' % mem, 'RAYON_NUM_THREADS=%d' % threads, HEAVY, P['prover'],
           os.path.join(P['air'], 'm5b%d.json' % D), dump, mode]
    with (PROVER_LOCK if mode == 'prove' else CHECK_SEM):
        t0 = time.time()
        p = subprocess.run(['nice', '-n', '10'] + cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           timeout=timeout)
        dt = time.time() - t0
    return p.returncode, p.stdout.decode(errors='replace'), dt


def parse_check(rec, rc, log, dt):
    rec['check_s'] = round(dt, 2)
    if 'PRECHECK OK' in log:
        rec['check'] = 'OK'
    else:
        m = re.search(r'^(PRECHECK FAIL.*|.*panicked.*|.*[Ee]rror.*)$', log, re.M)
        rec['check'] = 'FAIL:' + (m.group(1)[:300] if m else 'rc=%d' % rc)
        rec['check_log_tail'] = log[-1500:]
    m = re.search(r'^CELLS (\d+)', log, re.M)
    if m:
        rec['cells'] = int(m.group(1))
    m = re.search(r'^TABLE HTAPE .*height 2\^(\d+)', log, re.M)
    if m:
        rec['htape_h'] = int(m.group(1))
    m = re.search(r'^TABLE SHA512 .*height 2\^(\d+)', log, re.M)
    if m:
        rec['sha512_h'] = int(m.group(1))


def list_cases(corpora):
    out = []
    for c in corpora:
        d = '/data/illia/nearproof-deps/corpora/%s/d3' % c
        for n in sorted(os.listdir(d)):
            p = os.path.join(d, n)
            if n in ('mutants', 'ood') or not os.path.isfile(os.path.join(p, 'claim.bin')):
                continue
            out.append(p)
    return out


def cmd_run(a):
    P = paths(a.base)
    os.makedirs(P['work'], exist_ok=True)
    cases = list_cases(a.corpora.split(','))
    done = set()
    if os.path.exists(a.out):
        for line in open(a.out):
            r = json.loads(line)
            done.add((r['corpus'], r['case']))
    todo = [c for c in cases if (c.split('/')[-3], c.split('/')[-1]) not in done]
    if a.limit:
        todo = todo[::max(1, len(todo) // a.limit)][:a.limit] if a.spread else todo[:a.limit]
    print('cases %d, done %d, todo %d' % (len(cases), len(done), len(todo)), flush=True)
    global CHECK_SEM
    CHECK_SEM = threading.Semaphore(a.check_par)
    wlock = threading.Lock()
    fout = open(a.out, 'a')
    me = os.path.abspath(__file__)
    cnt = collections.Counter()
    t_start = time.time()

    def one(i_case):
        i, case = i_case
        wd = os.path.join(P['work'], 'w%06d' % i)
        try:
            p = subprocess.run(['nice', '-n', '5', sys.executable, '-I', me, 'case', '--base', a.base, case, wd],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=1800)
            try:
                rec = json.loads(p.stdout.decode().strip().splitlines()[-1])
            except Exception:  # noqa: BLE001
                rec = dict(corpus=case.split('/')[-3], case=case.split('/')[-1], status='error',
                           error='worker rc=%d: %s' % (p.returncode, p.stderr.decode(errors='replace')[-400:]))
            if rec.get('dump'):
                rc, log, dt = run_prover(P, rec['D'], rec['dump'], 'check', threads=1, mem='4G')
                parse_check(rec, rc, log, dt)
            rec.pop('dump', None)
        except subprocess.TimeoutExpired:
            rec = dict(corpus=case.split('/')[-3], case=case.split('/')[-1], status='error', error='timeout')
        finally:
            shutil.rmtree(wd, ignore_errors=True)
        with wlock:
            fout.write(json.dumps(rec, separators=(',', ':')) + '\n')
            fout.flush()
            cnt[(rec.get('status'), rec.get('gen', '-').split(':')[0], rec.get('check', '-')[:4])] += 1
            tot = sum(cnt.values())
            if tot % 200 == 0 or tot == len(todo):
                print('%d/%d %.0fs %s' % (tot, len(todo), time.time() - t_start,
                                          dict(sorted(cnt.items(), key=lambda x: -x[1])[:8])), flush=True)

    with ThreadPoolExecutor(a.jobs) as ex:
        list(ex.map(one, enumerate(todo)))
    fout.close()


def cmd_case(a):
    t0 = time.time()
    try:
        rec = do_case(a.base, a.case, a.wd)
    except Exception as e:  # noqa: BLE001
        rec = dict(corpus=a.case.rstrip('/').split('/')[-3], case=a.case.rstrip('/').split('/')[-1],
                   status='error', error='case:' + exc_label(e), tb=traceback.format_exc()[-1500:])
    rec['t_case'] = round(time.time() - t0, 2)
    print(json.dumps(rec, separators=(',', ':')))


def cmd_prove(a):
    """Re-run the pipeline on a sample of OK cases (spread over STB rows / cells) and prove."""
    P = paths(a.base)
    recs = [json.loads(line) for line in open(a.inp)]
    ok = [r for r in recs if r.get('status') == 'state' and r.get('check') == 'OK']
    ok.sort(key=lambda r: (r.get('cells', 0), r.get('stb', 0)))
    pick = []
    n = min(a.n, len(ok))
    for j in range(n):
        r = ok[min(len(ok) - 1, round(j * (len(ok) - 1) / max(1, n - 1)))]
        if r not in pick:
            pick.append(r)
    me = os.path.abspath(__file__)
    fout = open(a.out, 'a')
    for r in pick:
        case = '/data/illia/nearproof-deps/corpora/%s/d3/%s' % (r['corpus'], r['case'])
        wd = os.path.join(P['work'], 'prove-%s-%s' % (r['corpus'], r['case']))
        p = subprocess.run([sys.executable, '-I', me, 'case', '--base', a.base, case, wd],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        rec = json.loads(p.stdout.decode().strip().splitlines()[-1])
        out = dict(corpus=r['corpus'], case=r['case'], keys=rec.get('keys'), changes=rec.get('changes'),
                   D=rec.get('D'), stb=rec.get('stb'), cells=r.get('cells'), post_root=rec.get('post_root'))
        if rec.get('dump'):
            rc, log, dt = run_prover(P, rec['D'], rec['dump'], 'prove', mem='40G')
            m = re.search(r'TIME prove ([\d.]+)s verify ([\d.]+)s threads (\d+) peak_rss_kib (\d+) proof_bytes (\d+)', log)
            if m:
                out.update(prove_s=float(m.group(1)), verify_s=float(m.group(2)), threads=int(m.group(3)),
                           peak_rss_kib=int(m.group(4)), proof_bytes=int(m.group(5)))
            out['verify_ok'] = 'VERIFY OK' in log
            out['accepted'] = out['verify_ok'] and 'statement check (TAPE root + prev_state_root): OK' in log
            m = re.search(r'^PROOF (.*)$', log, re.M)
            out['proof_census'] = m.group(1)[:300] if m else None
            m = re.search(r'^SOUNDNESS (.*)$', log, re.M)
            out['soundness'] = m.group(1) if m else None
            out['wall_s'] = round(dt, 1)
            if not out['accepted']:
                out['log_tail'] = log[-1500:]
        else:
            out['gen'] = rec.get('gen')
        shutil.rmtree(wd, ignore_errors=True)
        fout.write(json.dumps(out) + '\n')
        fout.flush()
        print(json.dumps(out), flush=True)


# ------------------------------------------------------------------------------ summary
def pct(xs, qs=(0, 10, 25, 50, 75, 90, 99, 100)):
    xs = sorted(xs)
    if not xs:
        return '-'
    return '  '.join('p%d=%s' % (q, xs[min(len(xs) - 1, int(round(q / 100 * (len(xs) - 1))))]) for q in qs) + \
        '  mean=%.1f  n=%d' % (sum(xs) / len(xs), len(xs))


def hist(c, total=None, top=40):
    total = total or sum(c.values())
    return '\n'.join('  %7d  %6.2f%%  %s' % (v, 100 * v / total, k) for k, v in c.most_common(top))


def cmd_summary(a):
    recs = [json.loads(line) for line in open(a.inp)]
    L = []
    pr = L.append
    pr('M5a-9 state-circuit corpus census (M5b AIR at 61d19af1f; prover sha256 cc6d0a01…; D = smallest with 2^D >= working set)')
    pr('cases: %d' % len(recs))
    pr('\n== per corpus: status (reject / nochange / state / error) and state-case outcome')
    by = collections.defaultdict(collections.Counter)
    for r in recs:
        by[r['corpus']][r['status']] += 1
        if r['status'] == 'state':
            o = classify(r)
            by[r['corpus']]['state:' + o.split(':')[0]] += 1
    keys = ['reject', 'nochange', 'error', 'state', 'state:OK', 'state:CHECKFAIL', 'state:UNSUPPORTED', 'state:ERROR']
    pr('  %-7s ' % 'corpus' + ' '.join('%18s' % k for k in ['total'] + keys))
    for c in sorted(by, key=lambda x: int(x[3:])):
        pr('  %-7s ' % c + ' '.join('%18d' % v for v in [sum(by[c][k] for k in ('reject', 'nochange', 'error', 'state'))] + [by[c][k] for k in keys]))
    tot = collections.Counter()
    for c in by:
        tot.update(by[c])
    pr('  %-7s ' % 'all' + ' '.join('%18d' % v for v in [sum(tot[k] for k in ('reject', 'nochange', 'error', 'state'))] + [tot[k] for k in keys]))
    st = [r for r in recs if r['status'] == 'state']
    pr('\n== state cases (%d): outcome histogram (first failure)' % len(st))
    pr(hist(collections.Counter(classify(r) for r in st)))
    uns = [r for r in st if classify(r).startswith('UNSUPPORTED')]
    pr('\n== UNSUPPORTED cases (%d): distinct gap shapes per case (fault-tolerant first pass)' % len(uns))
    single = collections.Counter()
    nshapes = collections.Counter()
    anyshape = collections.Counter()
    for r in uns:
        sh = sorted(set(k.split('|', 1)[1] for k in r.get('gaps', {})))
        nshapes[len(sh)] += 1
        for s in sh:
            anyshape[s] += 1
        if len(sh) == 1:
            single[sh[0]] += 1
    pr('  number of distinct gap shapes per UNSUPPORTED case: %s' % dict(sorted(nshapes.items())))
    pr('  cases needing ONLY this one shape:')
    pr(hist(single, len(uns)))
    pr('  cases needing this shape (any):')
    pr(hist(anyshape, len(uns)))
    sets = collections.Counter(' + '.join(sorted(set(k.split('|', 1)[1] for k in r.get('gaps', {})))) or '(none: plan-only)'
                               for r in uns)
    pr('  gap-shape sets:')
    pr(hist(sets, len(uns), 25))
    occ = collections.Counter()
    for r in uns:
        for k, v in r.get('gaps', {}).items():
            occ[k] += v
    pr('  walk occurrences by kind|shape (all UNSUPPORTED cases):')
    pr(hist(occ, None, 30))
    # greedy fix order: how many more cases each additional shape unlocks
    pr('  (the probe is the unbatched first pass: capacity / plan-only failures such as VBITS are not in these')
    pr('   lists; every case with >= 128 working-set keys also needs VBITS, see the greedy and the keys buckets)')
    pr('\n== greedy: state cases fully covered after supporting shapes in this order')
    pr('  (needs = probe shapes + first failure + VBITS if keys >= 128; shapes hidden behind these, e.g. the')
    pr('   plan-only "final node over an in-memory child", can only show up once they are supported)')
    covered = sum(1 for r in st if classify(r) == 'OK')
    # a case's needs: the probe's shapes plus its first failure (a plan-only / capacity failure
    # such as VBITS is not seen by the unbatched probe)
    unc = [r for r in st if classify(r) != 'OK']
    # VBITS: a pre-state node's reader count must be < 2^7, and the root is read by every find and
    # change walk (raw count >= keys), so every case with >= 128 keys needs it too
    vb = 'version readers >= 2^7 (VBITS)'
    need = [set(k.split('|', 1)[1] for k in r.get('gaps', {})) | {classify(r).split(':', 1)[1]}
            | ({vb} if r['keys'] >= 128 else set()) for r in unc]
    have = set()
    pr('  now: %d / %d (%.2f%%)' % (covered, len(st), 100 * covered / max(1, len(st))))
    while True:
        gain = collections.Counter()
        for s in need:
            rest = s - have
            if len(rest) == 1:
                gain[next(iter(rest))] += 1
        if not gain:
            rem = [s - have for s in need if s - have]
            if not rem:
                break
            c2 = collections.Counter(x for s in rem for x in s)
            pick = c2.most_common(1)[0][0]
            have.add(pick)
            pr('  + %-60s (+0 alone; unblocks pairs)' % pick)
            continue
        pick, g = gain.most_common(1)[0]
        have.add(pick)
        covered += g
        pr('  + %-60s +%5d -> %d (%.2f%%)' % (pick, g, covered, 100 * covered / max(1, len(st))))
    fin = [r for r in st if r.get('fin_nodes')]
    pr('\n== extraction: state cases whose finalize reads witness nodes the main walk never read: %d' % len(fin))
    pr('   (extract_state.py at 61d19af1f drops them; outcome with its nodes_read -> with them)')
    pr(hist(collections.Counter('%s -> %s' % (r.get('gen_orig'), classify(r)) for r in fin), len(fin), 20))
    pr('\n== outcome by working-set size (keys) bucket')
    bk = collections.defaultdict(collections.Counter)
    for r in st:
        k = r['keys']
        b = '<=32' if k <= 32 else '33-64' if k <= 64 else '65-127' if k <= 127 else '128-255' if k <= 255 else '>=256'
        bk[b][classify(r).split(':')[0]] += 1
    for b in ('<=32', '33-64', '65-127', '128-255', '>=256'):
        n = sum(bk[b].values())
        pr('  keys %-8s %6d cases: %s' % (b, n, ', '.join('%s %d (%.1f%%)' % (k, v, 100 * v / n) for k, v in bk[b].most_common())))
    pr('  max keys among OK cases: %d' % max((r['keys'] for r in st if classify(r) == 'OK'), default=0))
    bad = [r for r in st if classify(r).split(':')[0] in ('CHECKFAIL', 'ERROR')]
    pr('\n== CHECKFAIL / ERROR state cases (%d; first 15 listed, all in the JSONL)' % len(bad))
    pr(hist(collections.Counter(classify(r) for r in bad)))
    for r in bad[:15]:
        pr('  %s/%s  %s  %s' % (r['corpus'], r['case'], classify(r), (r.get('check_log_tail') or r.get('gen_tb') or '')[-300:].replace('\n', ' | ')))
    errs = [r for r in recs if r['status'] == 'error']
    pr('\n== pipeline errors (%d)' % len(errs))
    pr(hist(collections.Counter(r.get('error', '')[:150] for r in errs), None, 20))
    ok = [r for r in st if classify(r) == 'OK']
    pr('\n== distributions (state cases: all / OK)')
    for f in ('keys', 'changes', 'deletes', 'D', 'n_trans', 'nodes', 'maxkey', 'maxval'):
        pr('  %-9s all: %s' % (f, pct([r.get(f, 0) for r in st])))
        pr('  %-9s OK : %s' % ('', pct([r.get(f, 0) for r in ok])))
    pr('  D histogram (all state): %s' % dict(sorted(collections.Counter(r.get('D') for r in st).items())))
    for f in ('stb', 'stw', 'cells', 'sha_blocks', 'comps', 'check_s'):
        pr('  %-9s OK : %s' % (f, pct([r.get(f) for r in ok if r.get(f) is not None])))
    for tb in ('STB', 'BR', 'SN', 'KEY', 'WSB', 'RNG', 'SNC'):
        pr('  rows %-4s OK: %s' % (tb, pct([r['rows'].get(tb, 0) for r in ok if 'rows' in r])))
    pr('  STB height 2^h (OK): %s' % dict(sorted(collections.Counter(r['heights'].get('STB') for r in ok if 'heights' in r).items())))
    pr('  HTAPE height 2^h (OK): %s' % dict(sorted(collections.Counter(r.get('htape_h') for r in ok).items())))
    pr('  SHA512 height 2^h (OK): %s' % dict(sorted(collections.Counter(r.get('sha512_h') for r in ok).items())))
    pr('  n_transitions (all accepted, extracted): %s' % dict(sorted(collections.Counter(r.get('n_trans') for r in recs if 'n_trans' in r).items())))
    pr('  post_root == header root (state cases): %s' % dict(collections.Counter(r.get('post_eq_header') for r in st)))
    pr('  lean_match (state cases): %s' % dict(collections.Counter(r.get('lean_match') for r in st)))
    ops = collections.Counter()
    for r in st:
        for k in r.get('spec_ops', {}):
            ops[k] += 1
    pr('\n== spec path cases (ptrie.apply_changes): state cases using each')
    pr(hist(ops, len(st)))
    im = [(r, x) for r in recs for x in r.get('implicit', [])]
    pr('\n== implicit transitions with changes (tracegen only, not checked): %d in %d cases' % (len(im), len({id(r) for r, _ in im})))
    pr(hist(collections.Counter(x.get('gen', '?') for _, x in im)))
    if im:
        pr('  keys: %s' % pct([x.get('keys', 0) for _, x in im]))
        pr('  changes: %s' % pct([x.get('changes', 0) for _, x in im]))
        pr('  stb (OK): %s' % pct([x['stb'] for _, x in im if x.get('stb') is not None]))
    if a.prove and os.path.exists(a.prove):
        pr('\n== prove sample')
        for line in open(a.prove):
            x = json.loads(line)
            pr('  %s/%s keys=%s changes=%s D=%s stb=%s cells=%s root=%s proof=%s B prove=%ss verify=%ss rss=%s MiB verify_ok=%s accepted=%s' % (
                x['corpus'], x['case'], x.get('keys'), x.get('changes'), x.get('D'), x.get('stb'), x.get('cells'),
                x.get('post_root'), x.get('proof_bytes'), x.get('prove_s'), x.get('verify_s'),
                (x.get('peak_rss_kib') or 0) // 1024, x.get('verify_ok'), x.get('accepted')))
    print('\n'.join(L))


COMPACT = ('corpus', 'case', 'status', 'n_trans', 'keys', 'changes', 'deletes', 'D', 'nodes', 'fin_nodes',
           'outcome', 'gen_orig', 'stb', 'cells', 'htape_h', 'BR', 'SN', 'KEY', 'gaps', 'implicit')


def cmd_compact(a):
    """Per-case compact records for the repo log: line 1 is the field list, then one JSON array per
    case (outcome = classify(): OK | CHECKFAIL:… | UNSUPPORTED:… | ERROR:…; gaps = the probe's
    {kind|shape: walks}; implicit = [[keys, changes, gen, stb], …])."""
    with open(a.out, 'w') as f:
        f.write(json.dumps(dict(fields=COMPACT)) + '\n')
        for line in open(a.inp):
            r = json.loads(line)
            rows = r.get('rows') or {}
            r = dict(r, outcome=classify(r) if r.get('status') == 'state' else None,
                     BR=rows.get('BR'), SN=rows.get('SN'), KEY=rows.get('KEY'),
                     gaps=r.get('gaps') or None,
                     implicit=[[x.get('keys'), x.get('changes'), x.get('gen'), x.get('stb')]
                               for x in r.get('implicit', [])] or None)
            f.write(json.dumps([r.get(k) for k in COMPACT], separators=(',', ':')) + '\n')


def classify(r):
    g = r.get('gen', 'ERROR:none')
    if g == 'OK':
        c = r.get('check')
        if c == 'OK':
            return 'OK'
        return 'CHECKFAIL:' + str(c)[:100]
    return g


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    r = sp.add_parser('run')
    r.add_argument('--base', required=True)
    r.add_argument('--jobs', type=int, default=8)
    r.add_argument('--limit', type=int, default=0)
    r.add_argument('--spread', action='store_true')
    r.add_argument('--check-par', type=int, default=8)
    r.add_argument('--corpora', default='d3c7,d3c8,d3c9,d3c10')
    r.add_argument('--out', required=True)
    c = sp.add_parser('case')
    c.add_argument('--base', required=True)
    c.add_argument('case')
    c.add_argument('wd')
    p = sp.add_parser('prove')
    p.add_argument('--base', required=True)
    p.add_argument('--in', dest='inp', required=True)
    p.add_argument('--n', type=int, default=15)
    p.add_argument('--out', required=True)
    s = sp.add_parser('summary')
    s.add_argument('--in', dest='inp', required=True)
    s.add_argument('--prove')
    k = sp.add_parser('compact')
    k.add_argument('--in', dest='inp', required=True)
    k.add_argument('--out', required=True)
    a = ap.parse_args()
    dict(run=cmd_run, case=cmd_case, prove=cmd_prove, summary=cmd_summary, compact=cmd_compact)[a.cmd](a)


if __name__ == '__main__':
    main()
