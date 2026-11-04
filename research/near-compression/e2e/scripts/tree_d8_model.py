"""E2E-D milestone D-8: the leaf-cost re-measurement and the 100 Tgas / 1 Pgas PROJECTION (model only;
nothing here ran on a GPU).

usage: tree_d8_model.py TREE_RUN_DIR LEAF_L_PROVE_LOG
  TREE_RUN_DIR: a D-8 arity-4 tree run whose setup has a class with an n_stack-22 base (class L),
                RESULT.json + prove.log (TREE_TEMPLATE pins per class, TREE_LEAF_PARAMS)
  LEAF_L_PROVE_LOG: the leaf-only run over the class-L base (leaf_ab_d8.sh; its NV_QCOST lines give
                the leaf's NvAir rows per WHIR query round)

What changed against tree_d7_model.py (D-7):
 1. Segment leaf size. D-7 scaled the measured D0a leaf (class A base: n_stack 18, lb 7) by the
    prover-budget model's compression count for a 2^22-row lb-1 segment (610 queries per round,
    the model's Johnson-regime law): x3.45. The stack's own WHIR calibration (`base-whir`: the
    pinned 268-bit target, ListDecoding m = 64, 32 grinding bits, the first-order certificates)
    gives the actual schedule: lb 1 at n_stack 22 is [97, 69, 41, 31] queries, sum(queries x Merkle
    depth) 5,192 against 3,055 for class A. And a leaf over an n_stack-22 base is *measured* in
    D-8: class L's base (n_stack 22, lb 2: [81, 60, 40, 30], 4,804) is a segment-geometry base.
    So the segment leaf = the measured class-L leaf, its SHA part scaled by 5,192 / 4,804.
 2. Leaf proof rate (the lever implemented in D-8): leaves are proved once per segment and
    verified only by P_2, so they run at ns20lb2 (rate 1/4; queries [81, 60, 40, 30]) instead of the
    tree's ns20lb5 (rate 1/32): the leaf's commitment (70 % of its GPU time at lb 5 in the model) is
    8x smaller, P_2 verifies more queries per leaf (measured in the D-8 arity-4 trees).
Everything else is tree_d7_model.py's schedule: 8 H200, arch b, adversarial workload, streaming
(segments released as execution produces them), list schedule, latency after execution.
"""
import json, math, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[1] / 'prover-budget'))
import model as M  # noqa: E402
from tree_d7_model import W, PROG_W, FRAC_PER_CELL, tree_counts, schedule  # noqa: E402

D7_A4_NODE = 542e6  # D-7 arity-4 P_2 over lb-5 leaves (tree_d7_model, results/zk/d7/model.txt)
# base-whir (results/zk/d8/base-whir.txt), n_stack 22: (sum of queries, sum(queries x Merkle depth))
# 'base config, 24-bit PoW': the base configuration with the seg-v1 grinding (NEARPROOF_BASE_WHIR_POW=24),
# so the segment prover's grinding stays at seg-v1's 2^24 per round (negligible on GPU)
SEG = {'base lb 1 (stack base config)': (246, 5366), 'base lb 2 (= class L)': (211, 4804),
       'seg-v1 lb 1 (lanes A/B today)': (961, 21789)}


def pin_cells(pin, prog_log):
    sha = sum(pin[a][1] for a in [1] + list(range(4, len(pin))))
    return pin[0][1] * W['nv'] + (1 << prog_log) * PROG_W, sha * W['sha'], pin[2][1] * W['table'] + pin[3][1] * W['byte']


def parse_pin(s):
    return [tuple(int(x) for x in t) for t in re.findall(r'\((\d+), Some\((\d+)\)\)', s)]


def gpu_s(p, cells, logn, lb):
    o, _, _ = M.ops_mf(p, 'b', cells, cells * FRAC_PER_CELL, lb, logn)
    return o / M.R(p)


def main():
    run = pathlib.Path(sys.argv[1])
    r = json.loads((run / 'RESULT.json').read_text())
    log = (run / 'prove.log').read_text(errors='replace')
    tm = {int(m.group(1)): (int(m.group(2)), parse_pin(m.group(3))) for m in re.finditer(r'TREE_TEMPLATE class=(\d+) kind=\w+ rows=(\d+) pin=(\[.*?\]) base_vk', log)}
    lp = re.search(r'TREE_LEAF_PARAMS n_stack=(\d+) log_blowup=(\d+)', log)
    leaf_lb = int(lp.group(2)) if lp else 5
    lg = r['leaf_geom']
    ng = r['node_geom']
    p = dict(M.P)
    print('== leaf sizes per class (measured template pins, committed cells: NvAir+program / SHA / tables) ==')
    per = {}
    for c, (rows, pin) in sorted(tm.items()):
        nv, sha, tb = pin_cells(pin, lg['prog_log'])
        per[c] = (nv, sha, tb)
        print(f'  class {c}: program rows {rows:,}; pin {pin}; cells {nv / 1e6:.1f} M + {sha / 1e6:.1f} M + {tb / 1e6:.1f} M = {(nv + sha + tb) / 1e6:.1f} M')
    big = max(per, key=lambda c: sum(per[c]))
    nv, sha, tb = per[big]
    ql = (pathlib.Path(sys.argv[2]).read_text(errors='replace'))
    qrows = sum(int(m.group(1)) for m in re.finditer(r'NV_QCOST round=\d+ queries=\d+ rows=(\d+)', ql)) // max(1, ql.count('TREE_TEMPLATE'))
    nv_tight = tm[big][1][0][1]
    q0, qd0 = SEG['base lb 2 (= class L)']
    segs = {}
    for name, (q, qd) in SEG.items():
        # SHA (Merkle + leaf hashing + transcript) scales with sum(q x depth); the NvAir rows of the
        # query rounds with sum(q); the rest of the leaf (preamble, DAG, sumchecks) is fixed
        nv_s = nv + (qrows * (q / q0 - 1)) * (nv_tight / tm[big][0]) * W['nv']
        segs[name] = nv_s + sha * qd / qd0 + tb
        print(f'  segment leaf, {name}: {segs[name] / 1e6:.0f} M cells (class-{big} leaf: SHA x {qd / qd0:.2f}, query NvAir rows x {q / q0:.2f})')
    seg_cells = segs['base lb 1 (stack base config)']
    d7_seg = 126e6 * 3.45
    print(f'  D-7 projection used {d7_seg / 1e6:.0f} M (the D0a leaf x 3.45 from the model\'s 610-query law)')
    node_cells = sum(pin_cells([tuple(h) for h in ng['heights']], ng['prog_log']))
    star_cells = node_cells * 1.13  # h_N = P_2 pin x 1.13 (D-8 margin at arity 4)
    wrap_cells = sum(pin_cells([tuple(h) for h in r['wrap_heights']], 18))
    print(f"  P_2 (arity {r['arity']}, measured node geometry {ng['log_rows']}/{ng['prog_log']}/{ng['sha_instances']}): {node_cells / 1e6:.0f} M cells; P_*/PAD_N at x1.13: {star_cells / 1e6:.0f} M")
    print('\n== PROJECTION (model only, not measured): 8 H200, arch b, adversarial workload, streaming ==')
    variants = [
        ('D-7 projection (x3.45 leaf, leaf lb 5)', d7_seg, 5, D7_A4_NODE),
        ('segments at seg-v1 (lanes today), leaf lb 5', segs['seg-v1 lb 1 (lanes A/B today)'], 5, D7_A4_NODE),
        (f'segments at seg-v1, leaf lb {leaf_lb}', segs['seg-v1 lb 1 (lanes A/B today)'], leaf_lb, None),
        ('segments at the base config, leaf lb 5', seg_cells, 5, D7_A4_NODE),
        (f'segments at the base config, leaf lb {leaf_lb} (D-8 recommendation)', seg_cells, leaf_lb, None),
    ]
    a = r['arity']
    for gas in (1e14, 1e15):
        rr = M.run(p, 'b', 'adv', gas)
        N = rr['n_seg']
        t_exec = rr['t_exec']
        t_base = rr['ops'] / N / M.R(p)
        print(f'  {gas / 1e12:,.0f} Tgas: {N} segments, execution {t_exec:.2f} s, base proof {t_base:.3f} GPU-s each (model)')
        for name, lc, llb, nco in variants:
            nc_ = nco or node_cells
            leaf = gpu_s(p, lc, 22, llb)
            n2 = gpu_s(p, nc_, ng['log_rows'] + 2, 5)
            ns = gpu_s(p, nc_ * 1.13, ng['log_rows'] + 2, 5)
            padl = gpu_s(p, sum(per[min(per)]), 21, llb)
            wrap = gpu_s(p, wrap_cells, 21, 5) * M.v(p, 'zk_time_factor')
            d, real, pl, pn = tree_counts(N, a)
            jobs = []
            for i in range(N):
                jobs.append((f'b{i}', t_base, t_exec * (i + 1) / N, []))
                jobs.append((f'l{i}', leaf, 0, [f'b{i}']))
            for j in range(pl):
                jobs.append((f'pl{j}', padl, 0, []))
            level = [f'l{i}' for i in range(N)] + [f'pl{j}' for j in range(pl)]
            for lv in range(d):
                if lv >= 1:
                    for j in range(pn[lv - 1]):
                        jobs.append((f'pn{lv}_{j}', ns, 0, []))
                        level.append(f'pn{lv}_{j}')
                nxt = []
                for j in range(0, len(level), a):
                    nm = f'n{lv}_{j // a}'
                    jobs.append((nm, n2 if lv == 0 else ns, 0, level[j:j + a]))
                    nxt.append(nm)
                level = nxt
            jobs.append(('wrap', wrap, 0, level))
            fin = schedule(M.v(p, 'n_gpu'), jobs)
            total = sum(j[1] for j in jobs)
            share = (N * (t_base + leaf)) / total
            print(f'    {name}: leaf {leaf:.3f}, P_2 {n2:.3f}, P_* {ns:.3f}, wrap {wrap:.3f} GPU-s; total {total:,.1f} GPU-s '
                  f'(segments + leaves {share:.0%}; leaves {N * leaf / total:.0%}); latency after execution {fin["wrap"] - t_exec:.2f} s')


if __name__ == '__main__':
    main()
