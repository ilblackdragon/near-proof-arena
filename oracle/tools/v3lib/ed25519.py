"""Ed25519 verification exactly as nearcore performs it (independent Python model).

Written from RFC 8032 §5.1 / §6 (reference code) with the deviations of the crates
nearcore pins (nearcore 44f7ae6, ed25519-dalek 2.2.0 without `legacy_compatibility`,
curve25519-dalek 4.1.3); NOT derived from the Lean formalization
(spec/lean/v3/NearSpecV3/Ed25519.lean), and deliberately built differently:
affine coordinates with the textbook Edwards addition law and modular inversion,
LSB-first double-and-add, square roots via RFC 8032 §5.1.3 `recover_x`
(x = (u/v)^((p+3)/8)), hashlib's SHA-512.

Deviations from RFC 8032 §5.1.3/§5.1.7 (dalek semantics, see Lean module docstring
for file:line citations):
  * public key y >= p (non-canonical, bit 255 cleared) is accepted and used mod p;
  * x = 0 with sign bit 1 is accepted (x stays 0);
  * R is never decoded: accept iff encode([s]B - [k]A) == sig[0:32] byte-for-byte;
  * s must satisfy s < L (from_canonical_bytes);
  * k = SHA-512(R_bytes || pk_bytes || msg) mod L over the ORIGINAL pk bytes;
  * cofactorless equation; small-order / mixed-order A allowed.

`verify(pk, sig, msg)` = nearcore's `verify_raw` verdict (no Borsh check);
`sig_encoding_ok(sig)` = nearcore's Borsh check `sig[63] & 0xE0 == 0`.

Selftest: `python3 -m v3lib.ed25519 DIR` (from oracle/tools) checks every *.jsonl in
DIR that has `verify_raw` / `sig_decodes` fields, and sha512.jsonl.
"""
import hashlib

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = (-121665 * pow(121666, P - 2, P)) % P
I = pow(2, (P - 1) // 4, P)  # sqrt(-1)

BY = (4 * pow(5, P - 2, P)) % P


def _recover_x(y, sign):
    """RFC 8032 §5.1.3 steps 2-4 with dalek's x=0/sign deviation; None if no root."""
    u = (y * y - 1) % P
    v = (D * y * y + 1) % P
    x2 = u * pow(v, P - 2, P) % P
    if x2 == 0:
        return 0  # dalek: -0 = 0, accepted for either sign bit
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P != 0:
        x = x * I % P
    if (x * x - x2) % P != 0:
        return None
    if x & 1 != sign:
        x = P - x
    return x


BX = _recover_x(BY, 0)
BASE = (BX, BY)
IDENT = (0, 1)


def _add(p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    t = D * x1 * x2 * y1 * y2 % P
    x3 = (x1 * y2 + y1 * x2) * pow(1 + t, P - 2, P) % P
    y3 = (y1 * y2 + x1 * x2) * pow(1 - t, P - 2, P) % P
    return (x3, y3)


def _mul(n, pt):
    acc = IDENT
    while n:
        if n & 1:
            acc = _add(acc, pt)
        pt = _add(pt, pt)
        n >>= 1
    return acc


def _neg(pt):
    return ((-pt[0]) % P, pt[1])


def _compress(pt):
    x, y = pt
    return (y | ((x & 1) << 255)).to_bytes(32, 'little')


def _decompress(b):
    n = int.from_bytes(b, 'little')
    sign = n >> 255
    y = (n & ((1 << 255) - 1)) % P  # non-canonical y accepted
    x = _recover_x(y, sign)
    if x is None:
        return None
    return (x, y)


def sig_encoding_ok(sig):
    return len(sig) == 64 and (sig[63] & 0xE0) == 0


def verify(pk, sig, msg):
    pk, sig, msg = bytes(pk), bytes(sig), bytes(msg)
    if len(pk) != 32 or len(sig) != 64:
        return False
    A = _decompress(pk)
    if A is None:
        return False
    Rb, s = sig[:32], int.from_bytes(sig[32:], 'little')
    if s >= L:
        return False
    k = int.from_bytes(hashlib.sha512(Rb + pk + msg).digest(), 'little') % L
    return _compress(_add(_mul(s, BASE), _mul(k, _neg(A)))) == Rb


# ---- helpers for vector generation (not used by verify) ----

def sign_with_scalar(a, prefix, A_bytes, msg):
    """Signature (R, s) with secret scalar a and nonce prefix, over A_bytes as given."""
    r = int.from_bytes(hashlib.sha512(prefix + msg).digest(), 'little') % L
    Rb = _compress(_mul(r, BASE))
    k = int.from_bytes(hashlib.sha512(Rb + A_bytes + msg).digest(), 'little') % L
    return Rb + ((r + k * a) % L).to_bytes(32, 'little')


def _selftest(dirpath):
    import glob
    import json
    import os
    bad = 0
    for f in sorted(glob.glob(os.path.join(dirpath, '*.jsonl'))):
        n = ok = 0
        for line in open(f):
            j = json.loads(line)
            if 'sha512' in j:
                n += 1
                if hashlib.sha512(bytes.fromhex(j['msg'])).hexdigest() == j['sha512']:
                    ok += 1
                else:
                    print('  MISMATCH sha512', j.get('id'))
                continue
            if 'verify_raw' not in j:
                continue
            n += 1
            pk, sig, msg = (bytes.fromhex(j[k]) for k in ('pk', 'sig', 'msg'))
            good = verify(pk, sig, msg) == j['verify_raw'] and \
                sig_encoding_ok(sig) == j['sig_decodes']
            if good:
                ok += 1
            else:
                print('  MISMATCH', os.path.basename(f), j['id'])
        bad += n - ok
        print(f'{os.path.basename(f)}: {ok}/{n} agree')
    print('TOTAL mismatches:', bad)
    return bad


if __name__ == '__main__':
    import sys
    sys.exit(1 if _selftest(sys.argv[1] if len(sys.argv) > 1 else
                            '../fixtures/v3/ed25519') else 0)
