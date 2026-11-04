"""E2E-D milestone D-6: 2-ary vs 8-ary aggregation tree for a 1 Pgas chunk.

Two views, both printed:
  (1) CPU, from lane D's measurements (D-5 / D-6 tree runs, `tree-arity` probe): a node's
      in-circuit work is per child (SHA-384 compressions and NvAir rows per verified child) plus a
      small fixed part, and its prove time is linear in committed cells at fixed geometry.
  (2) GPU, `../../prover-budget/model.py` (arch b, adversarial 1 Pgas), with the per-child
      compressions and the cells per compression re-anchored on the measured tree layer
      (`ns20lb5`, queries [54, 41, 31, 25]); fan-in 2 / 4 / 8 at the tree layer's rate (lb 5)
      and at the model's own best design.
usage: tree_arity_model.py [PROBE_SUMMARY.txt]   (TREE_ARITY_PROBE / TREE_ARITY_PROVED lines)
Research model only; no parameter of the stack changes.
"""
import math, pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'prover-budget'))
import model as M  # noqa: E402

# ---- measured (D-5 tree-a2d1, chunk 1; ZK-ARGUMENT 8.1; README 0)
MEAS = {
    # wrap over one node child: shape base (NvAir rows, SHA rows) = per-child cost + wrap fixed part
    'child_nv_rows': 331_484, 'child_sha_rows': 1_129_984,
    # 2-ary node: shape base
    'node2_nv_rows': 665_232, 'node2_sha_rows': 2_259_712,
    'node2_prove_s': 514.3, 'node2_rss_gb': 20.4,  # 8 threads, pinned tree heights below
    'tree_pin_nv': 739_540, 'tree_pin_sha': 2_794_560,
    'nv_w': 76, 'sha_w': 83, 'sha_rows_per_comp': 128,
    'max_log_height': 22,  # l_skip + n_stack at ns20lb5 (l_skip + n_stack + log_blowup <= 27)
}


def probe(path):
    """{arity: (program_rows, nv_used, sha_used, comps)} from TREE_ARITY_PROBE lines."""
    out, proved = {}, {}
    for l in pathlib.Path(path).read_text().splitlines():
        m = re.search(r'TREE_ARITY_PROBE arity=(\d+) .*program_rows=(\d+) used_rows=\[(\d+), (\d+),.*sha_compressions=(\d+)', l)
        if m:
            a, pr, nv, sha, c = map(int, m.groups())
            out[a] = (pr, nv, sha, c)
        m = re.search(r'TREE_ARITY_PROVED arity=(\d+) .*bytes=(\d+) gen_s=([\d.]+) total_s=([\d.]+)', l)
        if m:
            proved[int(m.group(1))] = (int(m.group(2)), float(m.group(3)), float(m.group(4)))
    return out, proved


def fit(points):
    """least squares rows = per_child * a + fixed."""
    xs = list(points)
    n = len(xs)
    mx = sum(xs) / n
    my = sum(points[x] for x in xs) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    b = sum((x - mx) * (points[x] - my) for x in xs) / sxx if sxx else my / mx
    return b, my - b * mx


def cpu_view(pr):
    print('== (1) CPU, measured tree layer (ns20lb5, 268.2 bits/round), 8 threads ==')
    if pr:
        per_nv, fix_nv = fit({a: v[1] for a, v in pr.items()})
        per_sha, fix_sha = fit({a: v[2] for a, v in pr.items()})
        per_prog, fix_prog = fit({a: v[0] for a, v in pr.items()})
        print(f'  probe fit (used rows = per child x a + fixed): NvAir {per_nv:,.0f} x a + {fix_nv:,.0f}; '
              f'SHA {per_sha:,.0f} x a + {fix_sha:,.0f} ({per_sha / MEAS["sha_rows_per_comp"]:,.0f} compressions per child); '
              f'program {per_prog:,.0f} x a + {fix_prog:,.0f}')
        for a, v in sorted(pr.items()):
            print(f'    arity {a}: program {v[0]:,} rows, NvAir {v[1]:,}, SHA {v[2]:,} ({v[3]:,} compressions)')
    else:
        per_nv, fix_nv = MEAS['child_nv_rows'], MEAS['node2_nv_rows'] - 2 * MEAS['child_nv_rows']
        per_sha, fix_sha = MEAS['child_sha_rows'], MEAS['node2_sha_rows'] - 2 * MEAS['child_sha_rows']
    cap = 1 << MEAS['max_log_height']
    cells2 = MEAS['tree_pin_nv'] * MEAS['nv_w'] + MEAS['tree_pin_sha'] * MEAS['sha_w']
    s_per_cell = MEAS['node2_prove_s'] / cells2
    gb_per_cell = MEAS['node2_rss_gb'] / cells2
    rows = {}
    print(f'  max AIR height 2^{MEAS["max_log_height"]} = {cap:,} rows; 2-ary node: {cells2 / 1e6:,.0f} M committed cells, '
          f'{MEAS["node2_prove_s"]:.0f} s, {MEAS["node2_rss_gb"]} GB')
    for a in (2, 3, 4, 8):
        nv = per_nv * a + fix_nv
        sha = per_sha * a + fix_sha
        pin_nv, pin_sha = nv * 1.11, sha * 1.24  # the D-5 pin margins over the 2-ary shape base
        inst = math.ceil(pin_sha / cap)
        cells = pin_nv * MEAS['nv_w'] + pin_sha * MEAS['sha_w']
        rows[a] = cells
        print(f'  arity {a}: NvAir {nv / 1e6:.2f} M rows (log {math.ceil(math.log2(pin_nv))}), SHA {sha / 1e6:.2f} M rows '
              f'-> {inst} SHA AIR instance(s) at 2^{MEAS["max_log_height"]}; {cells / 1e6:,.0f} M cells, '
              f'~{cells * s_per_cell:,.0f} s, ~{cells * gb_per_cell:.0f} GB (linear in cells)')
    # a template leaf at its own pinned heights (D-5 normaliser shape pin, chunk 1): what a leaf
    # costs when leaves do not share the node's heights
    leaf_cells = 285_876 * MEAS['nv_w'] + 1_090_560 * MEAS['sha_w']
    print(f'  template leaf at its own pin: {leaf_cells / 1e6:,.0f} M cells, ~{leaf_cells * s_per_cell:,.0f} s')
    print('  tree over N leaves, CPU work (8 threads) and critical path (node proofs in sequence):')
    print('    U  = built (D-5/D-6): every tree proof has the node heights; pad to arity^depth with level-1 PAD')
    print('    S  = two shapes (leaf heights != node heights; level-2 program P_2 != P_*, anchor (2, C_2)); not built')
    print('    SL = S + PAD at any level (one PAD proof per missing subtree; PAD_l at level-l heights); not built')
    for N in (8, 47, 64, 94, 512):
        for a in (2, 8):
            d = max(1, math.ceil(math.log(N, a) - 1e-9))
            leaves = a ** d
            nodes = sum(a ** l for l in range(d))
            u = (leaves + nodes) * rows[a]
            sh = leaves * leaf_cells + nodes * rows[a]
            real = [math.ceil(N / a ** l) for l in range(d + 1)]  # real proofs per level (0 = leaves)
            pads = [a * real[l] - real[l - 1] for l in range(1, d + 1)]  # missing children per level
            sl = N * leaf_cells + pads[0] * leaf_cells + sum(pads[1:]) * rows[a] + sum(real[1:]) * rows[a]
            crit = leaf_cells * s_per_cell + d * rows[a] * s_per_cell
            print(f'    N={N:4d} a={a}: depth {d}; U {leaves} leaves ({leaves - N} PAD) + {nodes} nodes = {u * s_per_cell / 3600:,.1f} h; '
                  f'S {sh * s_per_cell / 3600:,.1f} h; SL {sum(real[1:])} nodes + {sum(pads)} PAD = {sl * s_per_cell / 3600:,.1f} h; '
                  f'critical path {crit / 60:,.0f} min')
    return per_sha / MEAS['sha_rows_per_comp'], (per_nv * MEAS['nv_w'] + per_sha * MEAS['sha_w']) / (per_sha / MEAS['sha_rows_per_comp'])


def gpu_view(comps_child, cells_per_comp):
    print('\n== (2) GPU model (prover-budget/model.py, arch b, adversarial 1 Pgas, 8 H200) ==')
    p = dict(M.P)
    q = dict(p)
    # re-anchor: the model's comps_per_child(lb 5, logn 22) := the measured per-child compressions
    base = M.comps_per_child(p, 5, 22, 'b')
    q['whir_comps_anchor'] = (p['whir_comps_anchor'][0] * comps_child / base, 'D-6', 'measured tree layer')
    q['rec_cells_per_comp'] = (cells_per_comp, 'D-6', 'measured tree layer (used rows)')
    print(f'  re-anchored: model per-child comps at lb 5 {base:,.0f} -> measured {comps_child:,.0f}; '
          f'cells per compression {p["rec_cells_per_comp"][0]:,} -> {cells_per_comp:,.0f}')
    for label, pp in (('model anchors', p), ('lane-D anchors', q)):
        for seg in (22, 23):
            for k in (2, 4, 8):
                r = dict(pp)
                r['fan_in'] = (k, 'D-6', '')
                r['lb_node'] = (5, 'D-6', 'tree layer rate 1/32')
                r['seg_log_rows'] = (seg, 'D-6', '')
                x = M.run(r, 'b', 'adv')
                print(f'  {label:14s} seg 2^{seg} fan-in {k}: {x["n_seg"]} segments, depth {x["depth"]}, node comps '
                      f'{[round(c) for c in x["node_comps"]]}, agg {x["agg_gpu_s"]:.2f} GPU-s, nodes '
                      f'{"/".join(f"{t:.2f}" for t in x["t_nodes"])} s, crit {x["crit"]:.2f} s, latency {x["latency"]:.2f} s')
        best = M.best_design(pp, 'b', 'adv')[1]
        print(f'  {label:14s} best design: {best["design"]}, latency {best["latency"]:.2f} s')


if __name__ == '__main__':
    pr, proved = probe(sys.argv[1]) if len(sys.argv) > 1 else ({}, {})
    for a, (b, g, t) in sorted(proved.items()):
        print(f'  proved arity-{a} node: {b:,} B, trace gen {g:.0f} s, total {t:.0f} s')
    c, cpc = cpu_view(pr)
    gpu_view(c, cpc)
