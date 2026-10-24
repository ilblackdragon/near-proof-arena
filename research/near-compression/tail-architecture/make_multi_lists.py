#!/usr/bin/env python3
"""Combine every original source list in order; capacities are explicit fixed profiles."""
import argparse
import json
import struct
from pathlib import Path
from receipt_list_public import emit


def encode(parts):
    return b'NPMULF01' + struct.pack('<I', len(parts)) + b''.join(struct.pack('<Q', len(p)) + p for p in parts)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('exports', type=Path)
    p.add_argument('lists', type=Path)
    p.add_argument('output', type=Path)
    p.add_argument('--capacities', required=True)
    p.add_argument('cases', nargs='+')
    a = p.parse_args()
    caps = [int(x) for x in a.capacities.split(',')]
    assert caps and all(0 < c <= 1024 and c & (c-1) == 0 for c in caps)
    a.output.mkdir(exist_ok=True, parents=True)
    for case in a.cases:
        view = json.loads((a.exports / case / 'rcpt.json').read_text())
        assert len(view['lists']) == len(caps), 'must include every source list'
        parts = [(a.lists / f'{case}-list{i}.list').read_bytes() for i in range(len(caps))]
        assert all(p[8:40] == parts[0][8:40] for p in parts)
        public = b''.join(emit(p, c) for p, c in zip(parts, caps))
        (a.output / (case+'.multi')).write_bytes(encode(parts))
        (a.output / (case+'.public')).write_bytes(public)
        print(case, 'lists', len(parts), 'receipts', sum(len(x['rs']) for x in view['lists']))
