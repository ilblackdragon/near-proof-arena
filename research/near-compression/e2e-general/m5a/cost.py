#!/usr/bin/env python3
"""M5a AIR cost census of a dump: committed cells (used rows, before power-of-two padding) by
component, per trie node row and per working-set access.   cost.py DUMP_DIR NAMES_JSON

Cell prices: SHA-256 block = 17 rows × 544 = 9,248 cells (+ one 544-cell start row per message);
SHA-512 compression = 128 rows × 83 = 10,624 cells (native v4 chip)."""
import json
import struct
import sys

SHA_ROW, SHA_BLK = 544, 17
C512 = 128 * 83
ID_KEY, ID_BR, ID_SN = 1 << 24, 2 << 24, 3 << 24


def blocks(n):
    return (n + 9 + 63) // 64


def main():
    d, names = sys.argv[1], json.load(open(sys.argv[2]))
    st = json.load(open(d + '/stats.json'))
    msgs = json.load(open(d + '/sha_msgs.json'))
    widths = {t: len(names[t]) for t in ['KEY', 'BR', 'SN', 'KCMP', 'WSB', 'WSN', 'WSA']}
    rows = st['rows']
    sha = {'KEY': [0, 0], 'BR': [0, 0], 'SN': [0, 0]}
    for m in msgs:
        k = 'KEY' if m['id'] < ID_BR else ('BR' if m['id'] < ID_SN else 'SN')
        b = blocks(len(m['bytes']) // 2)
        sha[k][0] += 1
        sha[k][1] += b
    sha_cells = {k: v[0] * SHA_ROW + v[1] * SHA_BLK * SHA_ROW for k, v in sha.items()}
    D = names['D']
    n_ws, n_w = st['ws_keys'], st['changes']
    comp = {'WSB': 2 * 2 * n_ws, 'WSN': 2 * ((1 << D) - 1), 'WSA': n_w * (4 + 2 * D)}
    assert sum(comp.values()) == st['compressions'], (comp, st['compressions'])
    out = {}
    for t in widths:
        out[t] = dict(rows=rows[t], width=widths[t], cells=rows[t] * widths[t])
    for t in sha:
        out[t]['sha256_msgs'], out[t]['sha256_blocks'] = sha[t]
        out[t]['sha256_cells'] = sha_cells[t]
    for t in comp:
        out[t]['sha512_comps'] = comp[t]
        out[t]['sha512_cells'] = comp[t] * C512
    tot = lambda t: out[t]['cells'] + out[t].get('sha256_cells', 0) + out[t].get('sha512_cells', 0)
    node_rows = rows['BR'] + rows['SN']
    trie_total = tot('BR') + tot('SN')
    summary = dict(
        trie_node_rows=node_rows,
        br_cells_per_row=round(tot('BR') / rows['BR']),
        sn_cells_per_row=round(tot('SN') / rows['SN']),
        cells_per_trie_node_row=round(trie_total / node_rows),
        ws_keys=n_ws, writes=n_w,
        key_cells_per_key=round((tot('KEY') + tot('KCMP')) / n_ws),
        wsb_cells_per_key=round(tot('WSB') / n_ws),
        wsa_cells_per_write=round(tot('WSA') / max(n_w, 1)),
        wsn_cells=tot('WSN'),
        total_used_cells=sum(tot(t) for t in out))
    print(json.dumps(dict(tables=out, summary=summary), indent=1))


main()
