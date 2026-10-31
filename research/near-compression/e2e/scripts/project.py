"""8 x H200 latency projection through prover-budget/model.py (no GPU here; model only).

usage: project.py [--set name=value ...]   -> prints a JSON table
Rows: the e2e D0a chunks (no Wasm gas; the model's 4 MiB witness floor dominates), mainnet p99,
100 Tgas and 1 Pgas, for architecture (b) (the main stack's shape) and (a) for reference, both
the adversarial worst case and the measured realistic mix.
"""
import importlib.util, json, pathlib, sys
here = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('model', here.parents[1] / 'prover-budget/model.py')
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
p = m.parse_overrides(sys.argv[1:], m.P) if hasattr(m, 'parse_overrides') else m.P
rows = []
for label, gas in [('e2e D0a chunks (gas ~ 0; model floor at 1 Ggas)', 1e9), ('mainnet p99 18.45 Tgas', 18.45e12),
                   ('100 Tgas', 100e12), ('1 Pgas', 1e15)]:
    for arch in ('b', 'a'):
        for kind in ('adv', 'real'):
            d, r = m.best_design(p, arch, kind, gas)
            rows.append({'row': label, 'gas': gas, 'arch': arch, 'kind': kind,
                         'latency_s': round(r['latency'], 3),
                         'design': {k: d[k] for k in sorted(d) if isinstance(d[k], (int, float, str))} if isinstance(d, dict) else str(d),
                         **{k: (round(v, 3) if isinstance(v, float) else v) for k, v in r.items()
                            if k in ('gpu_s', 'base_gpu_s', 'agg_gpu_s', 'wrap_s', 'crit_s', 'levels', 'segments', 'proof_bytes')}})
# The chain as actually run here (not the model's optimal tree): a tiny D0a base, then
# `levels` 1-child NV levels at ns19/lb6 verifying a lb6 (L1: lb7) child of 2^21 stacked rows,
# the last one being the ZK wrap (x zk_time_factor). Each proof is split over the node's GPUs
# at wrap_split_eff (one proof at a time: the chain is sequential).
R = m.peak_int32(p) * m.v(p, 'eff')
split = m.v(p, 'wrap_gpus') * m.v(p, 'wrap_split_eff')
lvl = []
for i, lb_child in enumerate([7, 6, 6, 6, 6, 6]):
    n = m.node(p, 'b', 1, lb_child, 21, 6, 'sha384', 'sha384')
    s1 = n['ops'] / R * (m.v(p, 'zk_time_factor') if i == 5 else 1.0)
    lvl.append({'level': 'FINAL' if i == 5 else f'L{i + 1}', 'comps': round(n['comps']), 'ops': n['ops'],
                'one_gpu_s': round(s1, 3), 'node_s': round(s1 / split, 3)})
chain = {'levels': lvl, 'serial_one_gpu_s': round(sum(x['one_gpu_s'] for x in lvl), 3),
         'serial_split_8gpu_s': round(sum(x['node_s'] for x in lvl), 3),
         'note': 'base proof of a D0a chunk (2.3 M cells) is < 0.05 s at this rate and omitted'}
print(json.dumps({'budget_s': m.v(p, 'budget_s'), 'eff': m.v(p, 'eff'), 'n_gpu': m.v(p, 'n_gpu'),
                  'measured_chain_projection': chain, 'rows': rows}, indent=1))
