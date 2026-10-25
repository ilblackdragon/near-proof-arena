#!/usr/bin/env python3
"""Exact multilinear evaluations from run intervals without dense field columns.

An algebra experiment only: base-field challenges, no commitment/authentication.
Preparation is per-witness work and is included separately in reported timings.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import time
import numpy as np

P = 2013265921


def modsum(values):
    # Four products of canonical BabyBear elements fit in uint64.
    values = np.asarray(values, dtype=np.uint64)
    while values.size > 1:
        values = np.pad(values, (0, (-values.size) % 4))
        values = values.reshape(-1, 4).sum(axis=1, dtype=np.uint64) % P
    return int(values[0] % P) if values.size else 0


def prefix_weights(point):
    w = np.array([1], dtype=np.uint64)
    for r in point:
        w = np.concatenate((w * ((1-r) % P) % P, w * r % P))
    # Bound guarantees the integer cumsum cannot overflow before reduction.
    assert len(w) * (P-1) < 2**64
    return np.concatenate((np.array([0], dtype=np.uint64), np.cumsum(w) % P))


def encode(col):
    starts = np.concatenate(([0], np.flatnonzero(col[1:] != col[:-1])+1))
    ends = np.concatenate((starts[1:], [len(col)]))
    vals = col[starts]
    nonzero = vals != 0
    return starts[nonzero].astype(np.uint32), ends[nonzero].astype(np.uint32), vals[nonzero].astype(np.uint32)


def evaluate(runs, prefix):
    starts, ends, values = runs
    weights = (prefix[ends] + P - prefix[starts]) % P
    return modsum(values.astype(np.uint64) * weights)


def dense_fold(col, point):
    values = col.astype(np.uint64)
    for r in point:
        left, right = values[::2], values[1::2]
        values = (left + r * ((right + P - left) % P)) % P
    return int(values[0])


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--trace', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    with a.trace.open('rb') as f: log_h, width = struct.unpack('<II', f.read(8))
    height = 1 << log_h
    assert a.trace.stat().st_size == 8 + height*width*4
    data = np.memmap(a.trace, dtype='<u4', mode='r', offset=8, shape=(height, width))
    start = time.monotonic()
    runs = [encode(data[:, c]) for c in range(width)]
    preparation = time.monotonic()-start
    rows = []
    for seed in [20261023, 20261024]:
        point = [int(x) for x in np.random.default_rng(seed).integers(0,P,size=log_h)]
        start = time.monotonic(); prefix = prefix_weights(point)
        compact = [evaluate(r, prefix) for r in runs]
        compact_s = time.monotonic()-start
        start = time.monotonic()
        dense = [dense_fold(data[:, c], point) for c in range(width)]
        dense_s = time.monotonic()-start
        assert compact == dense
        rows.append({'seed': seed, 'virtual_evaluation_s': compact_s,
                     'dense_fold_s': dense_s, 'all_columns_equal': True,
                     'evaluations_sha256': hashlib.sha256(np.asarray(dense,dtype='<u4').tobytes()).hexdigest()})
    report = {'status':'EXACT_UNAUTHENTICATED_VIRTUAL_TRACE_EVALUATION',
              'trace':str(a.trace),'height':height,'width':width,
              'preparation_s':preparation, 'intervals':sum(len(r[0]) for r in runs),
              'interval_storage_bytes':sum(sum(x.nbytes for x in r) for r in runs),
              'dense_field_bytes':height*width*4,'runs':rows,
              'limitations':['No PCS or soundness claim: interval list is unauthenticated.',
                  'Base-field microbenchmark; production extension-field costs unmeasured.',
                  'Compression preparation is per-witness work; not free preprocessing.',
                  'Does not prove AIR constraints, bus balance or recursive composition.',
                  'Python/NumPy comparison is not a GPU or optimized Rust comparison.']}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__ == '__main__': main()
