#!/usr/bin/env python3
"""Lossless bit census of canonical trace columns; this is not a proof codec.

Every packed column is decoded and compared to its original field values.
Observed widths are witness-dependent and cannot be assumed by a verifier.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct
import time
import numpy as np


def census(path):
    start = time.monotonic()
    with path.open('rb') as f:
        log_h, width = struct.unpack('<II', f.read(8))
    height = 1 << log_h
    assert path.stat().st_size == 8 + height * width * 4
    data = np.memmap(path, dtype='<u4', mode='r', offset=8, shape=(height, width))
    cols = []
    encoded = hashlib.sha256()
    encoded.update(struct.pack('<II', log_h, width))
    source = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            source.update(block)
    for i in range(width):
        col = np.array(data[:, i])
        lo, hi = int(col.min()), int(col.max())
        assert hi < 2013265921, 'noncanonical BabyBear field element'
        bits = hi.bit_length()
        if bits:
            shifts = np.arange(bits, dtype=np.uint32)
            binary = ((col[:, None] >> shifts) & 1).astype(np.uint8)
            packed = np.packbits(binary.reshape(-1), bitorder='little')
            unpacked = np.unpackbits(packed, count=height*bits, bitorder='little')
            restored = np.sum(unpacked.reshape(height, bits).astype(np.uint32)
                              << shifts, axis=1, dtype=np.uint32)
        else:
            packed = np.array([], dtype=np.uint8)
            restored = np.zeros(height, dtype=np.uint32)
        assert np.array_equal(col, restored), f'column {i} roundtrip failed'
        encoded.update(bytes([bits]))
        encoded.update(packed.tobytes())
        cols.append({'column': i, 'min': lo, 'max': hi, 'bits': bits,
                     'nonzero': int(np.count_nonzero(col)),
                     'transitions': int(np.count_nonzero(col[1:] != col[:-1])),
                     'constant': lo == hi})
    bit_payload = sum(c['bits'] * height for c in cols)
    return {'path': str(path), 'input_sha256': source.hexdigest(),
            'height': height, 'width': width, 'cells': height * width,
            'raw_field_bytes': height * width * 4,
            'packed_bytes_including_widths_and_header': 8 + width + (bit_payload+7)//8,
            'packed_sha256': encoded.hexdigest(), 'roundtrip_exact': True,
            'bit_columns': sum(c['bits'] == 1 for c in cols),
            'zero_columns': sum(c['max'] == 0 for c in cols),
            'constant_columns': sum(c['constant'] for c in cols),
            'nonzero_cells': sum(c['nonzero'] for c in cols),
            'columns': cols, 'wall_s': time.monotonic()-start}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dump', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--tables', nargs='+', default=['sha_t', 'sha_r', 'rcpt', 'walk'])
    a = p.parse_args()
    report = {'status': 'LOSSLESS_TRACE_REPRESENTATION_CENSUS', 'tables': [],
              'limitations': ['Observed widths are witness-dependent, not static AIR bounds.',
                              'Storage compression does not automatically reduce PCS work.',
                              'A binary-field circuit must enforce reconstruction, canonical field arithmetic and all original constraints.',
                              'No proof, security or GPU speedup is established by this census.']}
    a.output.parent.mkdir(parents=True, exist_ok=True)
    for table in a.tables:
        row = census(a.dump/(table+'.bin'))
        report['tables'].append(row)
        a.output.write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items() if k != 'columns'}), flush=True)


if __name__ == '__main__':
    main()
