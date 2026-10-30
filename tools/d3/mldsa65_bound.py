#!/usr/bin/env python3
"""ML-DSA-65 (FIPS 204) key generation, signing and verification, with a boundary signer.

Used by the `mldsa` scenario of `oracle/v3-successor` (env `NEAR_MLDSA_BOUND_SIGNER`) to put
signatures whose `z` sits exactly at the norm bound into whole chunks (workplan item 10, W06).

near_crypto derives an ML-DSA-65 key from a 32-byte seed (`core/crypto/src/test_utils.rs:37-61`:
the seed string's bytes, truncated or padded with spaces to 32) through aws-lc's
`PqdsaKeyPair::from_seed`, i.e. FIPS 204 `ML-DSA.KeyGen_internal(ξ)`. The key holder can therefore
run `Sign_internal` with any mask `y` it likes: verification does not (and cannot) check how `y` was
chosen. `sign_bound` draws `y` as in Sign_internal, then moves one coefficient `y[p][j]` to
`T - e` with `e` drawn near the expected `(c·s1)[p][j]`, and accepts a candidate only when
`z[p][j] == ±T` exactly, every other `|z| < T`, and every other Sign_internal check passes
(`‖r0‖∞ < γ2 − β`, `‖c·t0‖∞ < γ2`, at most ω hints). With `T = γ1 − β` the result fails *only* the
`‖z‖∞ < γ1 − β` check of Verify (`verify(..., check_norm=False)` accepts it); with
`T = γ1 − β − 1` it is a valid signature whose largest coefficient is the largest allowed.

usage:
  mldsa65_bound.py pk SEED_STR                          -> pk hex
  mldsa65_bound.py sign SEED_STR MSG_HEX MODE [RNG]     -> sig hex   (MODE: at+ at- in+ in- honest)
  mldsa65_bound.py verify PK_HEX MSG_HEX SIG_HEX [--no-norm]  -> true/false
  mldsa65_bound.py selftest
Messages are signed as pure ML-DSA with an empty context (M' = 0x00 ‖ 0x00 ‖ M), as near_crypto /
aws-lc do.
"""
import hashlib
import random
import sys

Q = 8380417
N = 256
D = 13
TAU = 49
LAMBDA = 192
GAMMA1 = 1 << 19
GAMMA2 = (Q - 1) // 32
K, L = 6, 5
ETA = 4
BETA = TAU * ETA
OMEGA = 55
CT_LEN = LAMBDA // 4
SIG_LEN = CT_LEN + L * 640 + OMEGA + K
PK_LEN = 32 + K * 320


def shake256(b, n):
    return hashlib.shake_256(b).digest(n)


def shake128(b, n):
    return hashlib.shake_128(b).digest(n)


def bitrev8(x):
    return int(f"{x:08b}"[::-1], 2)


ZETAS = [pow(1753, bitrev8(k), Q) for k in range(256)]


def ntt(w):
    w = list(w)
    m, ln = 0, 128
    while ln >= 1:
        start = 0
        while start < 256:
            m += 1
            z = ZETAS[m]
            for j in range(start, start + ln):
                t = z * w[j + ln] % Q
                w[j + ln] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
            start += 2 * ln
        ln //= 2
    return w


def intt(w):
    w = list(w)
    m, ln = 256, 1
    while ln < 256:
        start = 0
        while start < 256:
            m -= 1
            z = Q - ZETAS[m]
            for j in range(start, start + ln):
                t = w[j]
                w[j] = (t + w[j + ln]) % Q
                w[j + ln] = z * (t - w[j + ln]) % Q
            start += 2 * ln
        ln *= 2
    f = 8347681
    return [x * f % Q for x in w]


def pmul(a, b):
    return [x * y % Q for x, y in zip(a, b)]


def padd(a, b):
    return [(x + y) % Q for x, y in zip(a, b)]


def psub(a, b):
    return [(x - y) % Q for x, y in zip(a, b)]


def modpm(r, a):
    r %= a
    if r > a // 2:
        r -= a
    return r


def centered(x):
    x %= Q
    return x - Q if x > Q // 2 else x


def inf_norm(vec):
    return max(abs(centered(x)) for p in vec for x in p)


def rej_ntt_poly(seed):
    out, buf, i = [], shake128(seed, 3 * 1024), 0
    while len(out) < 256:
        if i + 3 > len(buf):
            buf = shake128(seed, len(buf) * 2)
        b0, b1, b2 = buf[i], buf[i + 1], buf[i + 2] & 127
        i += 3
        z = (b2 << 16) | (b1 << 8) | b0
        if z < Q:
            out.append(z)
    return out


def rej_bounded_poly(seed):
    out, buf, i = [], shake256(seed, 1024), 0
    while len(out) < 256:
        z = buf[i]
        i += 1
        for b in (z & 15, z >> 4):
            if b < 9 and len(out) < 256:
                out.append((4 - b) % Q)
    return out


def expand_a(rho):
    return [[rej_ntt_poly(rho + bytes([s, r])) for s in range(L)] for r in range(K)]


def expand_s(rhop):
    s1 = [rej_bounded_poly(rhop + r.to_bytes(2, "little")) for r in range(L)]
    s2 = [rej_bounded_poly(rhop + (r + L).to_bytes(2, "little")) for r in range(K)]
    return s1, s2


def bits_pack(vals, nbits):
    acc, n, out = 0, 0, bytearray()
    for v in vals:
        acc |= v << n
        n += nbits
        while n >= 8:
            out.append(acc & 255)
            acc >>= 8
            n -= 8
    assert n == 0
    return bytes(out)


def bits_unpack(b, nbits, count):
    x = int.from_bytes(b, "little")
    return [(x >> (nbits * i)) & ((1 << nbits) - 1) for i in range(count)]


def matvec(A, vhat):
    return [intt([sum(A[r][s][j] * vhat[s][j] for s in range(L)) % Q for j in range(256)]) for r in range(K)]


def power2round(r):
    rp = r % Q
    r0 = modpm(rp, 1 << D)
    return (rp - r0) >> D, r0


def decompose(r):
    rp = r % Q
    r0 = modpm(rp, 2 * GAMMA2)
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // (2 * GAMMA2), r0


def use_hint(h, r):
    m = (Q - 1) // (2 * GAMMA2)
    r1, r0 = decompose(r)
    if h and r0 > 0:
        return (r1 + 1) % m
    if h:
        return (r1 - 1) % m
    return r1


def w1_encode(w1):
    return b"".join(bits_pack(p, 4) for p in w1)


def sample_in_ball(rho):
    buf = shake256(rho, 8 + 1024)
    h = int.from_bytes(buf[:8], "little")
    c = [0] * 256
    pos = 8
    for i in range(256 - TAU, 256):
        while True:
            j = buf[pos]
            pos += 1
            if j <= i:
                break
        c[i] = c[j]
        c[j] = 1 if ((h >> (i + TAU - 256)) & 1) == 0 else Q - 1
    return c


def seed_bytes(s):
    b = s.encode()[:32]
    return b + b" " * (32 - len(b))


def keygen(xi):
    hb = shake256(xi + bytes([K, L]), 128)
    rho, rhop, key = hb[:32], hb[32:96], hb[96:]
    A = expand_a(rho)
    s1, s2 = expand_s(rhop)
    t = [padd(p, q) for p, q in zip(matvec(A, [ntt(p) for p in s1]), s2)]
    t1, t0 = [], []
    for p in t:
        a, b = zip(*(power2round(x) for x in p))
        t1.append(list(a))
        t0.append(list(b))
    pk = rho + b"".join(bits_pack(p, 10) for p in t1)
    tr = shake256(pk, 64)
    return dict(pk=pk, rho=rho, key=key, tr=tr, A=A, s1=s1, s2=s2, t0=t0, t1=t1)


def hint_pack(h):
    y = bytearray(OMEGA + K)
    idx = 0
    for i in range(K):
        for j in range(256):
            if h[i][j]:
                y[idx] = j
                idx += 1
        y[OMEGA + i] = idx
    return bytes(y)


def sig_encode(ct, z, h):
    zb = b"".join(bits_pack([(GAMMA1 - centered(x)) for x in p], 20) for p in z)
    return ct + zb + hint_pack(h)


def mu_of(tr, msg):
    return shake256(tr + b"\x00\x00" + msg, 64)


def sign_bound(sk, msg, mode, rng):
    """mode: honest | at+ | at- | in+ | in- (see module doc)."""
    A, s1, s2, t0 = sk["A"], sk["s1"], sk["s2"], sk["t0"]
    s1h = [ntt(p) for p in s1]
    s2h = [ntt(p) for p in s2]
    t0h = [ntt(p) for p in t0]
    mu = mu_of(sk["tr"], msg)
    target = {"at": GAMMA1 - BETA, "in": GAMMA1 - BETA - 1}.get(mode[:2])
    sign = -1 if mode.endswith("-") else 1
    attempts = 0
    while True:
        attempts += 1
        y = [[modpm(rng.randrange(-GAMMA1 + 1, GAMMA1 + 1), Q) % Q for _ in range(256)] for _ in range(L)]
        if target is not None:
            p, j = rng.randrange(L), rng.randrange(256)
            e = int(round(rng.gauss(0, 18)))
            y[p][j] = (sign * target - e) % Q
        w = matvec(A, [ntt(p) for p in y])
        w1 = [[decompose(x)[0] for x in p] for p in w]
        ct = shake256(mu + w1_encode(w1), CT_LEN)
        ch = ntt(sample_in_ball(ct))
        cs1 = [intt(pmul(ch, p)) for p in s1h]
        cs2 = [intt(pmul(ch, p)) for p in s2h]
        z = [padd(a, b) for a, b in zip(y, cs1)]
        zc = [[centered(x) for x in p] for p in z]
        if target is None:
            if max(abs(x) for p in zc for x in p) >= GAMMA1 - BETA:
                continue
        else:
            if zc[p][j] != sign * target:
                continue
            rest = max(abs(x) for i, pp in enumerate(zc) for jj, x in enumerate(pp) if (i, jj) != (p, j))
            if rest >= GAMMA1 - BETA:
                continue
        wcs2 = [psub(a, b) for a, b in zip(w, cs2)]
        r0 = max(abs(decompose(x)[1]) for pp in wcs2 for x in pp)
        if r0 >= GAMMA2 - BETA:
            continue
        ct0 = [intt(pmul(ch, pp)) for pp in t0h]
        if inf_norm(ct0) >= GAMMA2:
            continue
        h = []
        for a, b in zip(ct0, wcs2):
            r = padd(b, a)
            h.append([1 if decompose(r[jj])[0] != decompose((r[jj] - a[jj]) % Q)[0] else 0 for jj in range(256)])
        if sum(map(sum, h)) > OMEGA:
            continue
        return sig_encode(ct, z, h), attempts


def verify(pk, msg, sig, check_norm=True):
    if len(pk) != PK_LEN or len(sig) != SIG_LEN:
        return False
    rho = pk[:32]
    t1 = [bits_unpack(pk[32 + 320 * i:32 + 320 * (i + 1)], 10, 256) for i in range(K)]
    ct = sig[:CT_LEN]
    z = [[(GAMMA1 - v) % Q for v in bits_unpack(sig[CT_LEN + 640 * i:CT_LEN + 640 * (i + 1)], 20, 256)] for i in range(L)]
    y = sig[CT_LEN + 640 * L:]
    h = [[0] * 256 for _ in range(K)]
    idx = 0
    for i in range(K):
        if y[OMEGA + i] < idx or y[OMEGA + i] > OMEGA:
            return False
        first = idx
        while idx < y[OMEGA + i]:
            if idx > first and y[idx - 1] >= y[idx]:
                return False
            h[i][y[idx]] = 1
            idx += 1
    if any(y[i] for i in range(idx, OMEGA)):
        return False
    if check_norm and inf_norm(z) >= GAMMA1 - BETA:
        return False
    A = expand_a(rho)
    tr = shake256(pk, 64)
    mu = mu_of(tr, msg)
    ch = ntt(sample_in_ball(ct))
    az = matvec(A, [ntt(p) for p in z])
    ct1 = [intt(pmul(ch, ntt([(x << D) % Q for x in p]))) for p in t1]
    wa = [psub(a, b) for a, b in zip(az, ct1)]
    w1 = [[use_hint(h[i][j], wa[i][j]) for j in range(256)] for i in range(K)]
    return shake256(mu + w1_encode(w1), CT_LEN) == ct


def max_z(sig):
    z = [bits_unpack(sig[CT_LEN + 640 * i:CT_LEN + 640 * (i + 1)], 20, 256) for i in range(L)]
    return max(abs(GAMMA1 - v) for p in z for v in p)


def main(a):
    if a[0] == "pk":
        print(keygen(seed_bytes(a[1]))["pk"].hex())
    elif a[0] == "sign":
        sk = keygen(seed_bytes(a[1]))
        rng = random.Random(a[4] if len(a) > 4 else None)
        sig, n = sign_bound(sk, bytes.fromhex(a[2]), a[3], rng)
        print(sig.hex())
        print(f"attempts={n} max|z|={max_z(sig)}", file=sys.stderr)
    elif a[0] == "verify":
        print("true" if verify(bytes.fromhex(a[1]), bytes.fromhex(a[2]), bytes.fromhex(a[3]), "--no-norm" not in a) else "false")
    elif a[0] == "selftest":
        sk = keygen(seed_bytes("selftest"))
        msg = bytes(range(32))
        for mode in ["honest", "at+", "at-", "in+", "in-"]:
            sig, n = sign_bound(sk, msg, mode, random.Random(mode))
            print(mode, n, max_z(sig), verify(sk["pk"], msg, sig), verify(sk["pk"], msg, sig, check_norm=False))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
