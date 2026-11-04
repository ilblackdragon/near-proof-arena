"""E2E-D D-8: a production set of pinned base shape classes over a heights census.

usage: classes_d8.py CENSUS_DIR OUT_DIR [--cuts Q1,Q2,...] [--headroom H] [--max-ns NS]

A class pins, per base AIR (AIR order, TAPE last), the log height L_t and the committed (tight)
height T_t, and the TAPE's log and key set (pq-state-port `TapePad`). Classes are *chosen*, not
found: since D-8 the generator grows any table past its render (`statedump --class`), so a chunk c
fits class K iff for every table t
  * L_t >= c's compact log l_ct (and L_t <= the table's maxLog), and
  * T_t >= c's committed rows at L_t: round4(last non-zero row) for a zero-padded table, 2^L_t for
    a table with a non-zero padding row (its re-cut fills the table);
  * TAPE: L_TAPE >= c's TAPE log, keys = the corpus's key universe (a superset of c's).
Classes are nested by size: chunks are ranked by their own natural committed cells, class i is the
per-coordinate maximum over the chunks up to rank quantile Q_i, grown by `headroom` (rows x (1 + H),
then the log rounded up and the tight height rounded up to 1/8 of 2^L), the last class over every
chunk (`--max-ns 22`: a class whose stacked height needs n_stack 22 pins its base rate to
`log_blowup` 2, as the two-adic bound 2 + n_stack + lb <= 27 requires; at the pinned lb 7, n_stack
<= 18). Classes are nested (each coordinate of class i+1 >= class i's).
Every chunk is assigned to the cheapest class admitting it; the report gives coverage, per-class
padding overhead (class committed cells / the chunk's natural committed cells) and the base
geometry (n_stack, w_stack) of each class (pq-state-port `params_for`).
Writes OUT_DIR/<class>.json (the PQ driver's / statedump's class format + tape_keys),
OUT_DIR/assign.json and prints the report."""
import argparse, json, math, pathlib, sys
from collections import Counter

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from census_stats_d8 import ORDER, load, padkind, tape_shape  # noqa: E402

TAPE_W = None  # set from the key universe


def need(h, kind, t, L):
    """committed rows table t of chunk h needs at log L (None if L is below its compact log)."""
    x = h[t]
    if L < x['log']:
        return None
    if kind[t] == 'zero':
        return max(4, -(-max(x['last_nonzero'], 1) // 4) * 4)
    return 1 << L


def natural(h, kind):
    """the chunk's own (D-7 'natural') shape: compact logs, tight per padding kind."""
    return {t: (h[t]['log'], need(h, kind, t, h[t]['log'])) for t in ORDER}


def cells(shape, widths):
    return sum(widths[t] * shape[t][1] for t in ORDER)


def full_cells(shape, widths, tape):
    return sum(widths[t] * (1 << shape[t][0]) for t in ORDER) + tape[1] * (1 << tape[0])


def base_geom(shape, widths, tape):
    """pq-state-port params_for('small'): (n_stack, w_stack) or None beyond n_stack 22."""
    total = full_cells(shape, widths, tape)
    maxh = max([1 << shape[t][0] for t in ORDER] + [1 << tape[0]])
    for n in (14, 18, 22):
        if (1 << (n + 2)) >= maxh and -(-total // (1 << (n + 2))) + 4 <= 24:
            return n, max(8, -(-total // (1 << (n + 2))) + 4)
    return None


def grow(shape_rows, kind, hr, maxlog):
    """class coordinates from required (log, rows) maxima with headroom hr."""
    out = {}
    for t in ORDER:
        lmin, rows = shape_rows[t]
        r = math.ceil(rows * (1 + hr))
        if kind[t] == 'zero':
            L = max(lmin, max(2, math.ceil(math.log2(max(r, 4)))))
            L = min(L, maxlog[t])
            q = max(4, (1 << L) >> 3)
            T = min(1 << L, -(-max(r, 4) // q) * q)
        else:
            L = max(lmin, max(2, math.ceil(math.log2(max(r, 4)))))
            L = min(L, maxlog[t])
            T = 1 << L
        out[t] = (L, T)
    return out


def fits(h, kind, K, tape_log):
    for t in ORDER:
        L, T = K[t]
        n = need(h, kind, t, L)
        if n is None or n > T:
            return False
    return h['TAPE']['log'] <= tape_log


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('census')
    ap.add_argument('out')
    ap.add_argument('--cuts', default='0.6,0.95')
    ap.add_argument('--headroom', type=float, default=0.25)
    ap.add_argument('--max-ns', type=int, default=22)
    ap.add_argument('--tail-lb', type=int, default=2)
    ap.add_argument('--names', default='S,M,L,X,Y')
    a = ap.parse_args()
    H = load(a.census)
    kind = padkind(H)
    first = next(iter(H.values()))
    widths = {t: first[t]['width'] for t in ORDER}
    maxlog = {t: first[t]['max_log'] for t in ORDER}
    keys = set()
    for d in sorted(pathlib.Path(a.census).iterdir()):
        f = d / 'pubmsgs.json'
        if f.exists() and d.name in H:
            keys |= {(b, len(m)) for b, s, m in json.loads(f.read_text())}
    keys = sorted(keys)
    tape_w = max(k[1] for k in keys) + 1 + len(keys)
    nat = {c: natural(h, kind) for c, h in H.items()}
    ncell = {c: cells(nat[c], widths) for c in H}
    # chunks whose own natural shape already exceeds the base geometry bound
    feas = {c for c in H if (g := base_geom(nat[c], widths, (H[c]['TAPE']['log'], tape_w))) and g[0] <= a.max_ns}
    prev = None
    order = sorted(feas, key=lambda c: ncell[c])
    cuts = [float(x) for x in a.cuts.split(',')] + [1.0]
    names = a.names.split(',')
    classes = []
    for i, q in enumerate(cuts):
        mem = order[:max(1, math.ceil(q * len(order)))]
        req = {t: (max(H[c][t]['log'] for c in mem), max(need(H[c], kind, t, H[c][t]['log']) if kind[t] == 'zero' else H[c][t]['used_rows'] + 1 for c in mem)) for t in ORDER}
        K = grow(req, kind, a.headroom, maxlog)
        tl = max(H[c]['TAPE']['log'] for c in mem)
        tl = max(tl, math.ceil(math.log2(max(4, max(H[c]['TAPE']['rows'] for c in mem) * (1 + a.headroom)))))
        g = base_geom(K, widths, (tl, tape_w))
        if g is None or g[0] > a.max_ns:
            # headroom pushed the class past the geometry bound: fall back to no headroom
            K = grow(req, kind, 0.0, maxlog)
            tl = max(H[c]['TAPE']['log'] for c in mem)
        if prev is not None:  # nested
            K = {t: (max(K[t][0], prev['K'][t][0]), max(K[t][1], prev['K'][t][1])) for t in ORDER}
            tl = max(tl, prev['tape_log'])
        g = base_geom(K, widths, (tl, tape_w))
        assert g is not None and g[0] <= a.max_ns, f'class {names[i]}: no base geometry'
        prev = {'name': names[i], 'K': K, 'tape_log': tl, 'geom': g, 'q': q}
        classes.append(prev)
    # assignment: cheapest admitting class
    assign, unc = {}, []
    for c in H:
        best = None
        for i, k in enumerate(classes):
            if fits(H[c], kind, k['K'], k['tape_log']):
                cc = cells(k['K'], widths)
                if best is None or cc < best[1]:
                    best = (i, cc)
        if best is None:
            unc.append(c)
        else:
            assign[c] = best[0]
    out = pathlib.Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    print(f'census {len(H)} chunks; {len(feas)} with a natural base geometry n_stack <= {a.max_ns}; key universe {keys} (TAPE width {tape_w}); headroom {a.headroom:.0%}')
    print('padding kinds: ' + ', '.join(f'{t}={kind[t]}' for t in ORDER))
    for i, k in enumerate(classes):
        K = k['K']
        mem = [c for c, j in assign.items() if j == i]
        ov = sorted(cells(K, widths) / ncell[c] for c in mem)
        heights = [list(K[t]) for t in ORDER] + [[k['tape_log'], 4]]
        js = {'name': k['name'], 'names': ORDER + ['TAPE'], 'heights': heights, 'tape_keys': [list(x) for x in keys]}
        if k['geom'][0] + 2 + 7 > 27:
            js['log_blowup'] = a.tail_lb
        (out / f"{k['name']}.json").write_text(json.dumps(js))
        pct = lambda p: ov[min(len(ov) - 1, int(p * (len(ov) - 1)))] if ov else float('nan')
        print(f"class {k['name']} (rank quantile {k['q']:.2f}): committed {cells(K, widths):,} cells, full {full_cells(K, widths, (k['tape_log'], tape_w)):,}; "
              f"base n_stack {k['geom'][0]}, w_stack {k['geom'][1]}, lb {7 if k['geom'][0] <= 18 else a.tail_lb}; TAPE log {k['tape_log']}; "
              f"assigned {len(mem)} ({len(mem) / len(H):.1%}); padding overhead (class / natural committed cells) "
              f"median {pct(0.5):.2f}x, p90 {pct(0.9):.2f}x, max {pct(1.0):.2f}x")
        print('   ' + ' '.join(f"{t}={K[t][0]}/{K[t][1]}" for t in ORDER))
    print(f'coverage {len(assign)}/{len(H)} = {len(assign) / len(H):.1%}; uncovered {len(unc)}')
    if unc:
        big = Counter()
        for c in unc:
            for t in ORDER:
                if H[c][t]['log'] > max(k['K'][t][0] for k in classes):
                    big[t] += 1
        print('  uncovered: tables above the largest class log:', dict(big.most_common()))
        print('  uncovered: natural committed cells', sorted(ncell[c] for c in unc)[:3], '...', max(ncell[c] for c in unc),
              '; natural base n_stack', Counter((base_geom(nat[c], widths, (H[c]['TAPE']['log'], tape_w)) or (None,))[0] for c in unc))
    (out / 'assign.json').write_text(json.dumps({'census': str(pathlib.Path(a.census).resolve()), 'headroom': a.headroom, 'cuts': cuts, 'classes': [k['name'] for k in classes], 'assign': {c: classes[i]['name'] for c, i in sorted(assign.items())},
                                                 'uncovered': sorted(unc), 'natural_cells': ncell}, indent=0))


if __name__ == '__main__':
    main()
