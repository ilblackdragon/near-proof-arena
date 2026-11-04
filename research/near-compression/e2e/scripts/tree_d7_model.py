"""E2E-D milestone D-7: aggregation-tree arity from measured per-proof costs, and a streaming
prover-time PROJECTION for 100 Tgas and 1 Pgas on 8 H200 (model only; nothing here was run on a GPU).

Inputs: the D-7 tree runs (RESULT.json: seconds per proof kind, leaf / node geometry) and, for an
arity proved only at depth 1, the TREE_STAR_PROBE line of its prove.log (P_* trace shape).
  usage: tree_d7_model.py RUN_DIR[=ARITY] ...
Two views:
  (1) CPU, this host (8 threads): work and critical path of a tree over N leaves with leaves at
      their own heights, two node shapes (P_2, P_*) and PAD at any level, per arity;
  (2) PROJECTION, 8 H200 (`../../prover-budget/model.py`, arch b, adversarial workload): segment
      count from the model; base segment proofs from the model; every tree proof's GPU time from its
      measured committed cells (model `ops_mf` at the tree layer's rate 1/32); the base leaf scaled
      to a 2^22-row segment by the model's per-child compressions; then a list schedule on 8 GPUs
      with segments released as execution streams them. Latency = wrap finish - end of execution.
Research model only; no parameter of the stack changes.
"""
import json, math, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'prover-budget'))
import model as M  # noqa: E402

W = {'nv': 76, 'sha': 83, 'table': 9, 'byte': 5}  # committed widths (TREE vk, measured D-6)
PROG_W = 4  # program part P0..P3 (cached, full height)
FRAC_PER_CELL = 87_097_600 / 254_084_224  # interactions per cell, model's main-stack anchor (MR)


def cells_of(geom):
    """committed cells of a proof at geometry `geom` (RESULT.json leaf_geom / node_geom)."""
    h = geom['heights']
    k = geom['sha_instances']
    sha_idx = [1] + [3 + i for i in range(1, k)]
    nv = h[0][1] * W['nv'] + (1 << geom['prog_log']) * PROG_W
    sha = sum(h[a][1] for a in sha_idx) * W['sha']
    return nv + sha + h[2][1] * W['table'] + h[3][1] * W['byte'], h[0][0]


def load(args):
    runs = {}
    for a in args:
        d, _, ar = a.partition('=')
        d = pathlib.Path(d)
        r = json.loads((d / 'RESULT.json').read_text())
        ar = int(ar or r['arity'])
        k = r['seconds_by_kind']
        e = runs.setdefault(ar, {'arity': ar})
        e['leaf_cells'], _ = cells_of(r['leaf_geom'])
        e['node_cells'], e['node_log'] = cells_of(r['node_geom'])
        e['p2_cells'] = e['node_cells']
        e['node_geom'] = r['node_geom']
        for kind in ('leaf_template', 'pad_leaf', 'node2', 'node_star', 'pad_node', 'wrap'):
            if kind in k:
                e.setdefault(kind, []).append(k[kind]['mean_s'])
        e['bundle'] = r['bundle_bytes']
        e['wrap_cells'] = pin_cells([tuple(h) for h in r['wrap_heights']], 18)
        log = (d / 'prove.log').read_text(errors='replace')
        m = re.search(r'TREE_STAR_PROBE arity=\d+ rows=(\d+) shape_pin=(\[.*?\]) info', log)
        if m:
            pin = [tuple(int(x) for x in t) for t in re.findall(r'\((\d+), Some\((\d+)\)\)', m.group(2))]
            e['star_probe_pin'] = pin
        m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)
        if m:
            e['rss_gb'] = max(e.get('rss_gb', 0), int(m.group(1)) / 1e6)
    for e in runs.values():
        for kind in ('leaf_template', 'pad_leaf', 'node2', 'node_star', 'pad_node', 'wrap'):
            if kind in e:
                e[kind] = sum(e[kind]) / len(e[kind])
    return runs


def pin_cells(pin, prog_log):
    sha = sum(pin[a][1] for a in [1] + list(range(4, len(pin))))
    return pin[0][1] * W['nv'] + (1 << prog_log) * PROG_W + sha * W['sha'] + pin[2][1] * W['table'] + pin[3][1] * W['byte']


def fill_star(runs):
    """P_* and PAD_N where only a depth-1 run exists. Every node-height proof (P_2, P_*, PAD_N) of a
    depth >= 2 tree is proved at one pin h_N >= both shapes, and a proof's time follows its committed
    heights, not its content (arity 2, depth 3: P_2 516 / 555 s, P_* 511-556 s, PAD_N 491-509 s at
    the same h_N). So h_N = max(P_2 pin, P_* probe pin) x 1.02, and node seconds = the depth-1 run's
    P_2 seconds x cells(h_N) / cells(P_2 pin). Without a probe (it does not fit P_2's NvAir log, which
    BIND forces on P_*): h_N = P_2 pin x 1.15. NB: P_*'s NvAir log height must equal its children's
    (BIND), so h_N can move the node geometry up one NvAir log (arity 3: 974,284 x 1.1 > 2^20)."""
    leaf = [e['leaf_template'] for e in runs.values() if 'leaf_template' in e]
    for e in runs.values():
        if 'leaf_template' not in e:
            e['leaf_template'] = sum(leaf) / len(leaf)
        if 'node_star' in e:
            e['node2_tree'] = e['node2']
            continue
        g = e['node_geom']
        p2 = [tuple(h) for h in g['heights']]
        c2 = pin_cells(p2, g['prog_log'])
        if 'star_probe_pin' in e:
            ps = e['star_probe_pin']
            hn = [(max(a[0], b[0]), max(a[1], b[1]) * 1.02) for a, b in zip(p2, ps)]
            note = 'P_*, PAD_N, P_2 at h_N = max(P_2 pin, P_* probe pin) x 1.02'
        else:
            hn = [(a[0], a[1] * (1.15 if i in (0, 1) or i >= 4 else 1)) for i, a in enumerate(p2)]
            note = 'P_*, PAD_N, P_2 at h_N = P_2 pin x 1.15 (no P_* probe)'
        f = pin_cells(hn, g['prog_log'] + 0) / c2
        e['node2_tree'] = e['node_star'] = e['pad_node'] = e['node2'] * f
        e['node_cells'] *= f
        e['star_note'] = f'{note}: P_2 seconds x {f:.2f}'
    return runs


def cpu_fit(runs):
    """node seconds = alpha + beta x committed cells, least squares over the measured P_2 proofs."""
    pts = [(e['p2_cells'], e['node2']) for e in runs.values()]
    n = len(pts)
    mx = sum(x for x, _ in pts) / n
    my = sum(y for _, y in pts) / n
    sxx = sum((x - mx) ** 2 for x, _ in pts)
    b = sum((x - mx) * (y - my) for x, y in pts) / sxx if sxx else 0.0
    return my - b * mx, b


def tree_counts(N, a):
    """(depth, real nodes per level >= 2, PAD_L, PAD_N per level) with PAD at any level."""
    d = max(1, math.ceil(math.log(N, a) - 1e-9))
    real = [N]
    for _ in range(d):
        real.append(math.ceil(real[-1] / a))
    pad_l = a * real[1] - N
    pad_n = [a * real[l + 1] - real[l] for l in range(1, d)]
    return d, real[1:], pad_l, pad_n


def cpu_view(runs):
    print('== (1) CPU, this host, 8 threads: measured per-proof seconds ==')
    for a, e in sorted(runs.items()):
        print(f"  arity {a}: node geometry (NvAir 2^{e['node_geom']['log_rows']}, program 2^{e['node_geom']['prog_log']}, "
              f"{e['node_geom']['sha_instances']} SHA instance(s)); node {e['node_cells'] / 1e6:,.0f} M cells, leaf {e['leaf_cells'] / 1e6:,.0f} M cells; "
              f"template leaf {e['leaf_template']:.0f} s, PAD_L {e['pad_leaf']:.0f} s, P_2 {e['node2']:.0f} s, "
              f"P_* {e['node_star']:.0f} s{' (' + e['star_note'] + ')' if 'star_note' in e else ''}, PAD_N {e['pad_node']:.0f} s, "
              f"wrap {e['wrap']:.0f} s; peak {e.get('rss_gb', 0):.1f} GB; packet {e['bundle']:,} B")
    if len(runs) >= 2:
        al, be = cpu_fit(runs)
        print(f'  node proof seconds ~ {al:,.0f} s + {be * 1e6:,.2f} s per M committed cells (least squares over the P_2 proofs): '
              f'a large fixed part, so per child a wider node is cheaper on CPU than its cells suggest')
    print('  tree over N leaves (two node shapes, PAD at any level): CPU work (h, 8 threads) / critical path (min)')
    for N in (8, 64, 94, 512, 1024):
        row = []
        for a, e in sorted(runs.items()):
            d, real, pl, pn = tree_counts(N, a)
            work = N * e['leaf_template'] + pl * e['pad_leaf'] + real[0] * e['node2_tree'] + sum(real[1:]) * e['node_star'] + sum(pn) * e['pad_node'] + e['wrap']
            crit = e['leaf_template'] + e['node2_tree'] + (d - 1) * e['node_star'] + e['wrap']
            row.append(f"a={a}: d {d}, {sum(real)} nodes + {pl + sum(pn)} PAD, {work / 3600:,.1f} h / {crit / 60:,.0f} min")
        print(f'    N={N:5d}  ' + ';  '.join(row))


def gpu_s(p, cells, logn):
    o, _, _ = M.ops_mf(p, 'b', cells, cells * FRAC_PER_CELL, 5, logn)
    return o / M.R(p)


def schedule(n_gpu, jobs):
    """list schedule: jobs = [(name, duration, release_time, deps)] in topological order."""
    free = [0.0] * n_gpu
    fin = {}
    for name, dur, rel, deps in jobs:
        ready = max([rel] + [fin[d] for d in deps])
        i = min(range(n_gpu), key=lambda j: max(free[j], ready))
        start = max(free[i], ready)
        free[i] = start + dur
        fin[name] = free[i]
    return fin


def projection(runs):
    p = dict(M.P)
    n_gpu = M.v(p, 'n_gpu')
    print('\n== (2) PROJECTION (model only, not measured): 8 H200, arch b, adversarial workload, streaming ==')
    seg_comps = M.comps_per_child(p, M.v(p, 'lb_base'), M.v(p, 'seg_log_rows'), 'b')
    d0a_comps = 1_124_480 / 128  # base leaf SHA shape base, D-6 (verifies a D0a base proof)
    print(f"  a base leaf over a 2^{M.v(p, 'seg_log_rows')}-row segment (lb {M.v(p, 'lb_base')}) verifies ~{seg_comps:,.0f} compressions "
          f"vs {d0a_comps:,.0f} for the D0a base: leaf cells scaled by {seg_comps / d0a_comps:.2f}")
    for gas in (1e14, 1e15):
        r = M.run(p, 'b', 'adv', gas)
        N = r['n_seg']
        t_exec = r['t_exec']
        t_base = r['ops'] / N / M.R(p)
        print(f"  {gas / 1e12:,.0f} Tgas: {N} segments of 2^{M.v(p, 'seg_log_rows')} rows, execution {t_exec:.2f} s, base proof {t_base:.2f} s each "
              f"(model); model's own tree (fan-in {M.v(p, 'fan_in')}, lb {M.v(p, 'lb_node')}): latency {r['latency']:.2f} s")
        for a, e in sorted(runs.items()):
            leaf = gpu_s(p, e['leaf_cells'] * seg_comps / d0a_comps, 22)
            n2 = gpu_s(p, e['node_cells'], e['node_log'] + 2)
            ns = n2 * e['node_star'] / e['node2_tree']
            padn = n2 * e['pad_node'] / e['node2_tree']
            padl = gpu_s(p, e['leaf_cells'], 21)
            wrap = gpu_s(p, e['wrap_cells'], 21) * M.v(p, 'zk_time_factor')
            d, real, pl, pn = tree_counts(N, a)
            jobs = []
            for i in range(N):
                rel = t_exec * (i + 1) / N
                jobs.append((f'b{i}', t_base, rel, []))
                jobs.append((f'l{i}', leaf, 0, [f'b{i}']))
            for j in range(pl):
                jobs.append((f'pl{j}', padl, 0, []))
            level = [f'l{i}' for i in range(N)] + [f'pl{j}' for j in range(pl)]
            for lv in range(d):
                if lv >= 1:
                    for j in range(pn[lv - 1]):
                        jobs.append((f'pn{lv}_{j}', padn, 0, []))
                        level.append(f'pn{lv}_{j}')
                nxt = []
                for j in range(0, len(level), a):
                    nm = f'n{lv}_{j // a}'
                    jobs.append((nm, n2 if lv == 0 else ns, 0, level[j:j + a]))
                    nxt.append(nm)
                level = nxt
            jobs.append(('wrap', wrap, 0, level))
            fin = schedule(n_gpu, jobs)
            total = sum(j[1] for j in jobs)
            print(f"    arity {a}: depth {d}; per proof GPU-s: leaf {leaf:.3f}, P_2 {n2:.3f}, P_* {ns:.3f}, PAD_N {padn:.3f}, wrap {wrap:.3f}; "
                  f"total {total:,.1f} GPU-s; latency after execution {fin['wrap'] - t_exec:.2f} s")


if __name__ == '__main__':
    runs = fill_star(load(sys.argv[1:]))
    cpu_view(runs)
    projection(runs)
