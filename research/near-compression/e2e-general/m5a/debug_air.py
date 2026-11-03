#!/usr/bin/env python3
"""Debug aid: evaluate one table's exported constraints on a dumped trace and print each failing
constraint with column names.   debug_air.py AIR_JSON NAMES_JSON DUMP_DIR TABLE [max]"""
import json
import struct
import sys

P = 2013265921


def load(path):
    b = open(path, 'rb').read()
    log, w = struct.unpack('<II', b[:8])
    h = 1 << log
    vals = struct.unpack('<%dI' % (h * w), b[8:])
    return [list(vals[r * w:(r + 1) * w]) for r in range(h)]


def ev(e, cur, nxt, pubs, sel):
    t = e[0]
    if t == 'c':
        return e[1] % P
    if t == 'v':
        return (nxt if e[2] else cur)[e[1]]
    if t == 'p':
        return pubs[e[1]] if e[1] < len(pubs) else 0
    if t == 'first':
        return sel[0]
    if t == 'last':
        return sel[1]
    if t == 'trans':
        return sel[2]
    if t == '+':
        return (ev(e[1], cur, nxt, pubs, sel) + ev(e[2], cur, nxt, pubs, sel)) % P
    if t == '*':
        return ev(e[1], cur, nxt, pubs, sel) * ev(e[2], cur, nxt, pubs, sel) % P
    return (-ev(e[1], cur, nxt, pubs, sel)) % P


def show(e, names):
    t = e[0]
    if t == 'c':
        return str(e[1])
    if t == 'v':
        return names[e[1]] + ("'" if e[2] else '')
    if t in ('first', 'last', 'trans', 'p'):
        return t + (str(e[1]) if t == 'p' else '')
    if t == '-':
        return '-(' + show(e[1], names) + ')'
    return '(' + show(e[1], names) + ' ' + t + ' ' + show(e[2], names) + ')'


def cols(e, acc):
    if e[0] == 'v':
        acc.add((e[1], e[2]))
    for x in e[1:]:
        if isinstance(x, list):
            cols(x, acc)
    return acc


def main():
    air = json.load(open(sys.argv[1]))
    names = json.load(open(sys.argv[2]))
    d, tname = sys.argv[3], sys.argv[4]
    mx = int(sys.argv[5]) if len(sys.argv) > 5 else 5
    ti = names['tables'].index(tname)
    t = air['tables'][ti]
    rows = load('%s/%s.bin' % (d, tname))
    pubs = list(struct.unpack('<16I', open(d + '/pubs.bin', 'rb').read()))
    nm = names[tname]
    h = len(rows)
    n = 0
    for r in range(h):
        sel = (int(r == 0), int(r == h - 1), int(r != h - 1))
        for ci, c in enumerate(t['constraints']):
            if ev(c, rows[r], rows[(r + 1) % h], pubs, sel):
                print('row', r, 'constraint', ci, ':', show(c, nm)[:400])
                print('   ', {nm[i] + ("'" if nx else ''): (rows[(r + 1) % h] if nx else rows[r])[i] for i, nx in sorted(cols(c, set()))})
                n += 1
                if n >= mx:
                    return


main()
