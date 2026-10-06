"""Ed25519 verification with nearcore's (ed25519-dalek 2.2.0 `verify`) semantics — the same
predicate as v3lib/ed25519.py `verify` (decompression and the challenge are taken from it
unchanged), computed in extended twisted-Edwards coordinates (no field inversion per group
operation, one at the end) and memoized per (pk, sig, msg) within a process.

`python3 -m v3lib.ed25519x [VECTORS_DIR]` checks it against v3lib.ed25519.verify on every
vector of oracle/fixtures/v3/ed25519 (nearcore-judged), plus random signatures.
"""
import functools
import hashlib

from . import ed25519 as _ref

P, L, D = _ref.P, _ref.L, _ref.D
D2 = 2 * D % P


def _ext(pt):
    x, y = pt
    return (x, y, 1, x * y % P)


def _add(p, q):
    """add-2008-hwcd-3 for a = -1 (complete on edwards25519: a square, d non-square)."""
    X1, Y1, Z1, T1 = p
    X2, Y2, Z2, T2 = q
    A = (Y1 - X1) * (Y2 - X2) % P
    B = (Y1 + X1) * (Y2 + X2) % P
    C = T1 * D2 % P * T2 % P
    DD = 2 * Z1 * Z2 % P
    E, F, G, H = B - A, DD - C, DD + C, B + A
    return (E * F % P, G * H % P, F * G % P, E * H % P)


def _mul(n, p):
    acc = (0, 1, 1, 0)
    while n:
        if n & 1:
            acc = _add(acc, p)
        p = _add(p, p)
        n >>= 1
    return acc


def _compress(p):
    X, Y, Z, _ = p
    zi = pow(Z, P - 2, P)
    x, y = X * zi % P, Y * zi % P
    return (y | ((x & 1) << 255)).to_bytes(32, 'little')


_B = _ext(_ref.BASE)
# fixed-base table: [2^i]B
_BT = []
_t = _B
for _ in range(256):
    _BT.append(_t)
    _t = _add(_t, _t)


def _mul_base(n):
    acc = (0, 1, 1, 0)
    i = 0
    while n:
        if n & 1:
            acc = _add(acc, _BT[i])
        n >>= 1
        i += 1
    return acc


@functools.lru_cache(maxsize=1 << 16)
def verify(pk, sig, msg):
    pk, sig, msg = bytes(pk), bytes(sig), bytes(msg)
    if len(pk) != 32 or len(sig) != 64:
        return False
    A = _ref._decompress(pk)
    if A is None:
        return False
    Rb, s = sig[:32], int.from_bytes(sig[32:], 'little')
    if s >= L:
        return False
    k = int.from_bytes(hashlib.sha512(Rb + pk + msg).digest(), 'little') % L
    negA = _ext(((-A[0]) % P, A[1]))
    return _compress(_add(_mul_base(s), _mul(k, negA))) == Rb


def _selftest(vdir):
    """Every nearcore-judged vector (`verify_raw` = nearcore's Signature::verify on the raw
    pk / sig / msg) of oracle/fixtures/v3/ed25519/*.jsonl, plus random inputs against the
    reference transcription."""
    import glob
    import json
    import os
    import random
    bad = n = 0
    for f in sorted(glob.glob(os.path.join(vdir, '*.jsonl'))):
        for line in open(f):
            j = json.loads(line)
            if 'verify_raw' not in j:
                continue
            pk, sig, msg = (bytes.fromhex(j[k]) for k in ('pk', 'sig', 'msg'))
            n += 1
            if verify(pk, sig, msg) != j['verify_raw']:
                bad += 1
                print('  MISMATCH', os.path.basename(f), j.get('id'))
    rnd = random.Random(7)
    for _ in range(300):
        pk = bytes(rnd.getrandbits(8) for _ in range(32))
        sig = bytes(rnd.getrandbits(8) for _ in range(63)) + bytes([rnd.getrandbits(5)])
        msg = bytes(rnd.getrandbits(8) for _ in range(32))
        n += 1
        if verify(pk, sig, msg) != _ref.verify(pk, sig, msg):
            bad += 1
    print("ed25519x: %d/%d agree with nearcore's verdicts / the reference" % (n - bad, n))
    return bad == 0


if __name__ == '__main__':
    import os
    import sys
    d = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                                           '..', '..', 'fixtures', 'v3', 'ed25519')
    sys.exit(0 if _selftest(d) else 1)
