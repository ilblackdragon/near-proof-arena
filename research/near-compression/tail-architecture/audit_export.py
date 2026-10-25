#!/usr/bin/env python3
"""Independent structural reader for experimental proof exports; NOT a verifier."""
import argparse
import hashlib
import json
from pathlib import Path


class Reader:
    def __init__(self, data):
        self.data = data
        self.pos = 0

    def take(self, n):
        if n < 0 or n > len(self.data)-self.pos:
            raise ValueError('truncated or oversized field')
        start = self.pos
        self.pos += n
        return self.data[start:self.pos]

    def integer(self):
        return int.from_bytes(self.take(8), 'little')

    def done(self):
        if self.pos != len(self.data):
            raise ValueError('trailing bytes')


def backend(data):
    r = Reader(data)
    if r.take(8) != b'NPLAB001':
        raise ValueError('backend version')
    n, logq, levels = [r.integer() for _ in range(3)]
    if (n, logq) != (64, 48) or not 1 <= levels <= 16:
        raise ValueError('unsupported geometry')
    def polys(expected):
        count = r.integer()
        if count != expected:
            raise ValueError('polynomial count mismatch')
        r.take(count*n*((logq+7)//8))
    cr, fu, bu, kappa, kappa1 = [r.integer() for _ in range(5)]
    r.take(cr*8)
    polys(kappa1)
    parts = []
    for _ in range(levels):
        start = r.pos
        multiplicity, tail = r.integer(), r.integer()
        if tail not in [0, 1]:
            raise ValueError('invalid tail flag')
        r.take(multiplicity*16)
        f, fu, fg, b, bu, bg, k, k1, u1, u2 = [r.integer() for _ in range(10)]
        r.take(8+256*4+8)  # nonce, projection, output norm
        polys(u1)
        polys(u2)
        polys((128+logq-1)//logq)
        parts.append({'multiplicity': multiplicity, 'tail': tail,
                      'u1_polys': u1, 'u2_polys': u2, 'bytes': r.pos-start})
    count = r.integer()
    if count > (len(data)-r.pos)//16:
        raise ValueError('oversized terminal part count')
    terminal_polys = 0
    for _ in range(count):
        rank, norm = r.integer(), r.integer()
        r.take(rank*n*2)
        terminal_polys += rank
    r.done()
    return {'levels': parts, 'terminal_parts': count,
            'terminal_polys': terminal_polys,
            'terminal_coefficient_bytes': terminal_polys*n*2}


def packet(data):
    if len(data) > 16*1024*1024:
        raise ValueError('packet cap')
    r = Reader(data)
    if r.take(8) != b'NPTMPL01':
        raise ValueError('packet version')
    names = ['public_root', 'tape', 'claimed_f162', 'left_rns',
             'opening_rns', 'norms', 'labrador']
    parts = {name: r.take(r.integer()) for name in names}
    r.done()
    if len(parts['public_root']) != 64 or len(parts['claimed_f162']) != 21:
        raise ValueError('public/field size mismatch')
    if len(parts['norms']) % 8:
        raise ValueError('norm framing')
    info = backend(parts['labrador'])
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'sections': {k: len(v) for k, v in parts.items()}, 'backend': info}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('packets', type=Path, nargs='+')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    results = []
    for path in a.packets:
        data = path.read_bytes()
        result = packet(data)
        checks = [data[:-1], data+b'\0', data[:8]+b'\xff'*8+data[16:]]
        for mutant in checks:
            try:
                packet(mutant)
            except ValueError:
                continue
            raise AssertionError('malformed framing accepted')
        results.append({'file': str(path), **result, 'framing_mutants_rejected': len(checks)})
    report = {'status': 'EXPORT_STRUCTURE_ONLY_NOT_VERIFIED_FROM_BYTES',
              'packets': results, 'cryptographic_verification_from_bytes': False,
              'limitations': ['No native decoder or fresh-process proof verification yet.',
                  'RNS images are implementation-specific; no portable canonical codec claim.',
                  'Statement, capacity policy and setup identity are external pinned context.',
                  'No full NEAR relation, recursive history or composed PQ claim.']}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
