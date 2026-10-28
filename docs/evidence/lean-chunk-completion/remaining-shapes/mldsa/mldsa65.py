"""Compact pure-Python ML-DSA-65 (FIPS 204): KeyGen_internal, Sign_internal (with an optional
skip of the ||z|| rejection), Verify. Pure ML-DSA, empty context: M' = 0x00 || 0x00 || msg."""
import hashlib

Q = 8380417
D = 13
TAU = 49
LAM = 192
G1 = 1 << 19
G2 = (Q - 1) // 32
K, L, ETA = 6, 5, 4
BETA = TAU * ETA
OMEGA = 55
ZB = G1 - BETA  # 524092: verify requires ||z||_inf < ZB


def H(b, n):
    return hashlib.shake_256(b).digest(n)


def brv8(x):
    return int(f"{x:08b}"[::-1], 2)


ZETAS = [pow(1753, brv8(i), Q) for i in range(256)]
NINV = 8347681


def ntt(a):
    w = list(a)
    m, ln = 0, 128
    while ln >= 1:
        st = 0
        while st < 256:
            m += 1
            z = ZETAS[m]
            for j in range(st, st + ln):
                t = z * w[j + ln] % Q
                w[j + ln] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
            st += 2 * ln
        ln //= 2
    return w


def intt(a):
    w = list(a)
    m, ln = 256, 1
    while ln < 256:
        st = 0
        while st < 256:
            m -= 1
            z = Q - ZETAS[m]
            for j in range(st, st + ln):
                t = w[j]
                w[j] = (t + w[j + ln]) % Q
                w[j + ln] = z * (t - w[j + ln]) % Q
            st += 2 * ln
        ln *= 2
    return [x * NINV % Q for x in w]


def pmul(a, b):
    return [x * y % Q for x, y in zip(a, b)]


def padd(a, b):
    return [(x + y) % Q for x, y in zip(a, b)]


def psub(a, b):
    return [(x - y) % Q for x, y in zip(a, b)]


def matvec(Ah, vh):
    out = []
    for i in range(K):
        acc = [0] * 256
        for j in range(L):
            acc = padd(acc, pmul(Ah[i][j], vh[j]))
        out.append(intt(acc))
    return out


def cmod(r, m):  # r mod± m
    r0 = r % m
    if r0 > m // 2:
        r0 -= m
    return r0


def centered(x):
    x %= Q
    return x - Q if x > Q // 2 else x


def rej_ntt_poly(seed):
    xof = hashlib.shake_128(seed)
    buf = xof.digest(840 * 3)
    out, p = [], 0
    while len(out) < 256:
        if p + 3 > len(buf):
            buf = xof.digest(len(buf) * 2)
        v = buf[p] | buf[p + 1] << 8 | (buf[p + 2] & 0x7F) << 16
        p += 3
        if v < Q:
            out.append(v)
    return out


def rej_bounded_poly(seed):
    xof = hashlib.shake_256(seed)
    buf = xof.digest(1024)
    out, p = [], 0
    while len(out) < 256:
        if p >= len(buf):
            buf = xof.digest(len(buf) * 2)
        z = buf[p]
        p += 1
        for b in (z & 15, z >> 4):
            if b < 9 and len(out) < 256:
                out.append((4 - b) % Q)
    return out


def expand_a(rho):
    return [[rej_ntt_poly(rho + bytes([s, r])) for s in range(L)] for r in range(K)]


def bitpack(coeffs, bits):
    n = 0
    for i, c in enumerate(coeffs):
        n |= c << (bits * i)
    return n.to_bytes(len(coeffs) * bits // 8, "little")


def bitunpack(b, bits, cnt=256):
    n = int.from_bytes(b, "little")
    m = (1 << bits) - 1
    return [(n >> (bits * i)) & m for i in range(cnt)]


def expand_mask(rhopp, kappa):
    ys = []
    for r in range(L):
        v = H(rhopp + (kappa + r).to_bytes(2, "little"), 640)
        ys.append([(G1 - x) % Q for x in bitunpack(v, 20)])
    return ys


def sample_in_ball(ct):
    xof = hashlib.shake_256(ct)
    buf = xof.digest(8 + 1024)
    h = int.from_bytes(buf[:8], "little")
    c = [0] * 256
    p = 8
    for i in range(256 - TAU, 256):
        while True:
            j = buf[p]
            p += 1
            if j <= i:
                break
        c[i] = c[j]
        c[j] = 1 if ((h >> (i + TAU - 256)) & 1) == 0 else Q - 1
    return c


def decompose(r):
    rp = r % Q
    r0 = cmod(rp, 2 * G2)
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // (2 * G2), r0


def highbits(r):
    return decompose(r)[0]


def lowbits(r):
    return decompose(r)[1]


def use_hint(h, r):
    r1, r0 = decompose(r)
    if h and r0 > 0:
        return (r1 + 1) % 16
    if h:
        return (r1 - 1) % 16
    return r1


def w1encode(w1):
    return b"".join(bitpack(p, 4) for p in w1)


def keygen(xi):
    s = H(xi + bytes([K, L]), 128)
    rho, rhop, key = s[:32], s[32:96], s[96:]
    Ah = expand_a(rho)
    s1 = [rej_bounded_poly(rhop + r.to_bytes(2, "little")) for r in range(L)]
    s2 = [rej_bounded_poly(rhop + (r + L).to_bytes(2, "little")) for r in range(K)]
    s1h = [ntt(p) for p in s1]
    t = [padd(p, q) for p, q in zip(matvec(Ah, s1h), s2)]
    t1, t0 = [], []
    for p in t:
        a0 = [cmod(x, 1 << D) for x in p]
        t0.append([x % Q for x in a0])
        t1.append([(x - y) >> D for x, y in zip(p, a0)])
    pk = rho + b"".join(bitpack(p, 10) for p in t1)
    tr = H(pk, 64)
    return pk, dict(rho=rho, key=key, tr=tr, Ah=Ah, s1h=s1h, s2h=[ntt(p) for p in s2],
                    t0h=[ntt(p) for p in t0])


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
    return ct + b"".join(bitpack([(G1 - x) % Q for x in p], 20) for p in z) + hint_pack(h)


def sign_attempts(sk, msg, rnd, max_iter, accept):
    """Sign_internal(sk, 0x00||0x00||msg, rnd) with the ||z|| < γ1−β check replaced by
    accept(maxabs_z) (all other checks kept). Yields (kappa, sig, maxabs_z) for every κ whose
    attempt passes the remaining checks and accept(); max_iter bounds the κ loop."""
    mu = H(sk["tr"] + b"\x00\x00" + msg, 64)
    rhopp = H(sk["key"] + rnd + mu, 64)
    kappa = 0
    for _ in range(max_iter):
        y = expand_mask(rhopp, kappa)
        kappa += L
        w = matvec(sk["Ah"], [ntt(p) for p in y])
        w1 = [[highbits(x) for x in p] for p in w]
        ct = H(mu + w1encode(w1), LAM // 4)
        ch = ntt(sample_in_ball(ct))
        cs1 = [intt(pmul(ch, p)) for p in sk["s1h"]]
        z = [padd(a, b) for a, b in zip(y, cs1)]
        mz = max(abs(centered(x)) for p in z for x in p)
        if not accept(mz):
            continue
        cs2 = [intt(pmul(ch, p)) for p in sk["s2h"]]
        wm = [psub(a, b) for a, b in zip(w, cs2)]
        if max(abs(lowbits(x)) for p in wm for x in p) >= G2 - BETA:
            continue
        ct0 = [intt(pmul(ch, p)) for p in sk["t0h"]]
        if max(abs(centered(x)) for p in ct0 for x in p) >= G2:
            continue
        h = [[int(highbits(r) != highbits((r + c) % Q)) for r, c in zip(wp, cp)]
             for wp, cp in zip(padd_v(wm, ct0), [[(-x) % Q for x in p] for p in ct0])]
        if sum(map(sum, h)) > OMEGA:
            continue
        yield kappa - L, sig_encode(ct, z, h), mz


def padd_v(a, b):
    return [padd(x, y) for x, y in zip(a, b)]


def sign(sk, msg, rnd=bytes(32)):
    return next(sign_attempts(sk, msg, rnd, 1 << 16, lambda m: m < ZB))[1]


def hint_unpack(y):
    h = [[0] * 256 for _ in range(K)]
    idx = 0
    for i in range(K):
        if y[OMEGA + i] < idx or y[OMEGA + i] > OMEGA:
            return None
        first = idx
        while idx < y[OMEGA + i]:
            if idx > first and y[idx - 1] >= y[idx]:
                return None
            h[i][y[idx]] = 1
            idx += 1
    if any(y[i] for i in range(idx, OMEGA)):
        return None
    return h


def maxabs_z(sig):
    return max(abs(centered(G1 - x)) for r in range(L)
               for x in bitunpack(sig[48 + 640 * r: 48 + 640 * (r + 1)], 20))


def verify(pk, msg, sig, prefix=b"\x00\x00"):
    if len(pk) != 1952 or len(sig) != 3309:
        return False
    rho = pk[:32]
    t1 = [bitunpack(pk[32 + 320 * i: 32 + 320 * (i + 1)], 10) for i in range(K)]
    ct = sig[:48]
    z = [[(G1 - x) % Q for x in bitunpack(sig[48 + 640 * r: 48 + 640 * (r + 1)], 20)] for r in range(L)]
    h = hint_unpack(sig[48 + 3200:])
    if h is None:
        return False
    Ah = expand_a(rho)
    mu = H(H(pk, 64) + prefix + msg, 64)
    ch = ntt(sample_in_ball(ct))
    zh = [ntt(p) for p in z]
    w = []
    for i in range(K):
        acc = [0] * 256
        for j in range(L):
            acc = padd(acc, pmul(Ah[i][j], zh[j]))
        acc = psub(acc, pmul(ch, ntt([x << D for x in t1[i]])))
        w.append(intt(acc))
    w1 = [[use_hint(hb, x) for hb, x in zip(hp, wp)] for hp, wp in zip(h, w)]
    ok_z = max(abs(centered(x)) for p in z for x in p) < ZB
    return ok_z and H(mu + w1encode(w1), 48) == ct


def nearcore_xi(seed: str) -> bytes:
    """near_crypto test_utils::ml_dsa_65_seed_bytes_from_str: the seed string, space-padded to 32."""
    b = seed.encode()[:32]
    return b + b" " * (32 - len(b))
