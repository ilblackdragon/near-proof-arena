#!/usr/bin/env python3
"""Generate the BLS12-381 differential fixtures.

Every fixture line is the *oracle's own verdict* — `bls-oracle <host> <hexinput> <version>` — over
inputs constructed here. The oracle is a verbatim transcription of nearcore 44f7ae6c
`runtime/near-vm-runner/src/logic/bls12381.rs` over blst 0.3.11 (see
`oracle/bls-oracle/src/main.rs`), so the fixtures pin the Lean payloads to the source's behaviour
without this script itself modelling any curve arithmetic except to *construct* valid points.

Output: `oracle/fixtures/v3/bls12381/<host>.jsonl`, one JSON object per line:
`{"host": ..., "input": "<hex>", "version": 0, "res": <u64>, "out": "<hex>"|null}`.
"""
import json, os, random, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE = os.path.join(HERE, "bls-oracle", "target", "debug", "bls-oracle")
OUTDIR = os.path.join(HERE, "fixtures", "v3", "bls12381")

p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
r = 52435875175126190479447740508185965837690552500527637822603658699938581184513

def be(x, n):
    return x.to_bytes(n, "big").hex()

# --- G1 ------------------------------------------------------------------------------------
G1x = 0x17F1D3A73197D7942695638C4FA9AC0FC3688C4F9774B905A14E3A3F171BAC586C55E83FF97A1AEFFB3AF00ADB22C6BB
G1y = 0x08B3F481E3AAA0F1A09E30ED741D8AE4FCF5E095D5D00AF600DB18CB2C04B3EDD03CC744A2888AE40CAA232946C5E7E1

def g1_unc(x, y):
    """96-byte uncompressed G1: x ‖ y."""
    return be(x, 48) + be(y, 48)

def g1_inf():
    """96-byte uncompressed infinity: 0x40 ‖ zeros."""
    return "40" + "00" * 95

def _set_flags(b: bytes, comp=True, inf=False, sign=0) -> bytes:
    """Set the compression/infinity/sign flags in the top byte of a 48-byte big-endian element."""
    b0 = b[0]
    b0 = b0 & 0x1F                       # clear the three flag bits
    if comp: b0 |= 0x80
    if inf: b0 |= 0x40
    if sign: b0 |= 0x20
    return bytes([b0]) + b[1:]

def g1_comp(x, y, sign_bit=None):
    """48-byte compressed G1: the compression bit in the top byte, plus the sign bit of y."""
    s = (1 if y > (p - 1) // 2 else 0) if sign_bit is None else sign_bit
    return _set_flags(x.to_bytes(48, "big"), comp=True, sign=s).hex()

def g1_comp_inf():
    return _set_flags(bytes(48), comp=True, inf=True).hex()

# --- G2 ------------------------------------------------------------------------------------
G2x0 = 0x024AA2B2F08F0A91260805272DC51051C6E47AD4FA403B02B4510B647AE3D1770BAC0326A805BBEFD48056C8C121BDB8
G2x1 = 0x13E02B6052719F607DACD3A088274F65596BD0D09920B61AB5DA61BBDC7F5049334CF11213945D57E5AC7D055D042B7E
G2y0 = 0x0CE5D527727D6E118CC9CDC6DA2E351AADFD9BAA8CBDD3A76D429A695160D12C923AC9CC3BACA289E193548608B82801
G2y1 = 0x0606C4A02EA734CC32ACD2B02BC28B99CB3E287E85A763AF267492AB572E99AB3F370D275CEC1DA1AAA9075FF05F79BE

def g2_unc(x0, x1, y0, y1):
    """192-byte uncompressed G2: x1 ‖ x0 ‖ y1 ‖ y0."""
    return be(x1, 48) + be(x0, 48) + be(y1, 48) + be(y0, 48)

def g2_inf():
    return "40" + "00" * 191

def g2_comp(x0, x1, y0, y1, sign_bit=None):
    """96-byte compressed G2: (x1 ‖ x0) with the flags in the top byte of x1."""
    s = (1 if y1 > (p - 1) // 2 else 0) if sign_bit is None else sign_bit
    return _set_flags(x1.to_bytes(48, "big"), comp=True, sign=s).hex() + be(x0, 48)

def g2_comp_inf():
    return _set_flags(bytes(48), comp=True, inf=True).hex() + "00" * 48

def neg_y(y):
    return (p - y) % p

def g1_neg_enc(x, y):
    return g1_unc(x, neg_y(y))

def g2_neg_enc(x0, x1, y0, y1):
    return g2_unc(x0, x1, neg_y(y0), neg_y(y1))

# --- misc ----------------------------------------------------------------------------------
def le32(n):
    return n.to_bytes(32, "little").hex()

def g1_not_in_group():
    """A point on `y² = x³ + 4` that is *not* in the order-`r` subgroup."""
    x = 1
    while True:
        rhs = (pow(x, 3, p) + 4) % p
        y = pow(rhs, (p + 1) // 4, p)
        if (y * y) % p == rhs and y != 0:
            # cofactor is 0x396c8c005555e1568c00aaab0000aaab; r*P != O means not in G1
            if not _g1_is_in_group(x, y):
                return g1_unc(x, y)
        x += 1

def _g1_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        lam = (3 * x1 * x1) * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)

def _g1_mul(k, P):
    R = None
    for i in range(k.bit_length() - 1, -1, -1):
        R = _g1_add(R, R)
        if (k >> i) & 1: R = _g1_add(R, P)
    return R

def _g1_is_in_group(x, y):
    return _g1_mul(r, (x, y)) is None

def g2_not_in_group():
    """A point on the twist that is *not* in G2."""
    x0 = 1
    while True:
        # y² = x³ + 4(u+1) with x = x0 + 0·u
        # (x0)³ + 4 + 4u  → need sqrt in Fp2
        rhs = ((pow(x0, 3, p) + 4) % p, 4)
        y = _fp2_sqrt(rhs)
        if y is not None:
            if not _g2_is_in_group(((x0, 0), y)):
                return g2_unc(x0, 0, y[0], y[1])
        x0 += 1

def _fp2_mul(a, b):
    return ((a[0]*b[0] - a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)

def _fp2_inv(a):
    n = (a[0]*a[0] + a[1]*a[1]) % p
    ni = pow(n, p - 2, p)
    return (a[0]*ni % p, (-a[1]*ni) % p)

def _fp2_sqrt(a):
    if a[1] == 0:
        r = pow(a[0], (p + 1) // 4, p)
        return (r, 0) if r * r % p == a[0] % p else None
    n = (a[0]*a[0] + a[1]*a[1]) % p
    s = pow(n, (p + 1) // 4, p)
    if s * s % p != n: return None
    ti = pow(2, p - 2, p)
    for cand in ((a[0] + s) % p, (a[0] - s) % p):
        x0sq = cand * ti % p
        x0 = pow(x0sq, (p + 1) // 4, p)
        if x0 * x0 % p == x0sq and x0 != 0:
            x1 = a[1] * pow(2 * x0 % p, p - 2, p) % p
            rr = (x0, x1)
            return rr if _fp2_mul(rr, rr) == a else ((p - x0) % p, (p - x1) % p)
    return None

def _g2_add(P, Q):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and _fp2_mul(y1, y1) == _fp2_mul(y2, y2) and (y1[0] + y2[0]) % p == 0:
        return None
    if P == Q:
        num = _fp2_mul((3, 0), _fp2_mul(x1, x1))
        den = _fp2_inv(_fp2_mul((2, 0), y1))
    else:
        num = (y2[0] - y1[0]) % p, (y2[1] - y1[1]) % p
        den = _fp2_inv(((x2[0] - x1[0]) % p, (x2[1] - x1[1]) % p))
    lam = _fp2_mul(num, den)
    x3 = (lambda a, b: ((a[0] - b[0]) % p, (a[1] - b[1]) % p))(
        _fp2_mul(lam, lam), ((x1[0] + x2[0]) % p, (x1[1] + x2[1]) % p))
    y3 = _fp2_mul(lam, ((x1[0] - x3[0]) % p, (x1[1] - x3[1]) % p))
    return (x3, ((y3[0] - y1[0]) % p, (y3[1] - y1[1]) % p))

def _g2_mul(k, P):
    R = None
    for i in range(k.bit_length() - 1, -1, -1):
        R = _g2_add(R, R)
        if (k >> i) & 1: R = _g2_add(R, P)
    return R

def _g2_is_in_group(P):
    return _g2_mul(r, P) is None

# --- oracle --------------------------------------------------------------------------------
def ask(host, inp, version=0):
    out = subprocess.run([ORACLE, host, inp, str(version)], capture_output=True, text=True)
    res, hexout = None, None
    for line in out.stdout.splitlines():
        if line.startswith("res "):
            res = int(line.split()[1])
        elif line.startswith("out"):
            parts = line.split(None, 1)
            hexout = parts[1] if len(parts) > 1 else ""
        elif line.startswith("err "):
            res = "err"
        elif line.strip() == "-":
            hexout = None
        elif hexout is None and res is None and len(line) > 40:
            hexout = line.strip()
    return res, hexout

def main():
    os.makedirs(OUTDIR, exist_ok=True)
    random.seed(20261023)
    lines = {}

    def rec(host, inp, version=0):
        res, out = ask(host, inp, version)
        lines.setdefault(host, []).append(
            {"host": host, "input": inp, "version": version, "res": res, "out": out})
        return res, out

    # ---- p1_sum: (sign u8, 96B point)* -----------------------------------------------------
    g1gen = g1_unc(G1x, G1y)
    rec("bls12381_p1_sum", "00" + g1gen)                                   # one positive
    rec("bls12381_p1_sum", "01" + g1gen)                                   # one negative
    rec("bls12381_p1_sum", "00" + g1gen + "00" + g1gen)                    # P + P = 2P
    rec("bls12381_p1_sum", "00" + g1gen + "01" + g1gen)                    # P - P = O
    rec("bls12381_p1_sum", "")                                             # empty -> infinity
    rec("bls12381_p1_sum", "00" + g1_inf())                                # infinity input
    rec("bls12381_p1_sum", "02" + g1gen)                                   # bad sign byte -> 1
    rec("bls12381_p1_sum", "00" + "00" * 96)                               # (0,0) -> not on curve
    # not-in-group point: rejected only at version 1
    ng1 = g1_not_in_group()
    rec("bls12381_p1_sum", "00" + ng1, 0)
    rec("bls12381_p1_sum", "00" + ng1, 1)
    # (0, ±2) corner case: on curve, x = 0
    rec("bls12381_p1_sum", "00" + g1_unc(0, 2), 0)
    rec("bls12381_p1_sum", "00" + g1_unc(0, 2), 1)
    # top bit set on the point -> 1
    rec("bls12381_p1_sum", "00" + "80" + "00" * 95)
    # bad length
    rec("bls12381_p1_sum", "00" + g1gen[:-2])

    # ---- p2_sum ---------------------------------------------------------------------------
    g2gen = g2_unc(G2x0, G2x1, G2y0, G2y1)
    rec("bls12381_p2_sum", "00" + g2gen)
    rec("bls12381_p2_sum", "01" + g2gen)
    rec("bls12381_p2_sum", "00" + g2gen + "01" + g2gen)
    rec("bls12381_p2_sum", "")
    rec("bls12381_p2_sum", "00" + g2_inf())
    rec("bls12381_p2_sum", "05" + g2gen)
    rec("bls12381_p2_sum", "00" + "00" * 192)
    ng2 = g2_not_in_group()
    rec("bls12381_p2_sum", "00" + ng2, 0)
    rec("bls12381_p2_sum", "00" + ng2, 1)
    rec("bls12381_p2_sum", "00" + g2gen[:-2])

    # ---- g1_multiexp: (96B point, 32B LE scalar)* ------------------------------------------
    rec("bls12381_g1_multiexp", g1gen + le32(1))
    rec("bls12381_g1_multiexp", g1gen + le32(0))
    rec("bls12381_g1_multiexp", g1gen + le32(r + 5))
    rec("bls12381_g1_multiexp", g1gen + le32(2**255))
    rec("bls12381_g1_multiexp", "")
    rec("bls12381_g1_multiexp", g1gen + le32(1) + g1_neg_enc(G1x, G1y) + le32(1))
    rec("bls12381_g1_multiexp", ng1 + le32(1), 0)
    rec("bls12381_g1_multiexp", ng1 + le32(1), 1)
    rec("bls12381_g1_multiexp", g1gen + le32(1)[:-2])

    # ---- g2_multiexp ----------------------------------------------------------------------
    rec("bls12381_g2_multiexp", g2gen + le32(1))
    rec("bls12381_g2_multiexp", g2gen + le32(0))
    rec("bls12381_g2_multiexp", g2gen + le32(r + 3))
    rec("bls12381_g2_multiexp", "")
    rec("bls12381_g2_multiexp", ng2 + le32(1), 0)
    rec("bls12381_g2_multiexp", ng2 + le32(1), 1)

    # ---- p1_decompress --------------------------------------------------------------------
    rec("bls12381_p1_decompress", g1_comp(G1x, G1y))
    rec("bls12381_p1_decompress", g1_comp(G1x, G1y, 1 - (1 if G1y > (p - 1) // 2 else 0)))
    rec("bls12381_p1_decompress", g1_comp_inf())
    rec("bls12381_p1_decompress", "")
    rec("bls12381_p1_decompress", g1_comp(G1x, G1y) + g1_comp(G1x, G1y))
    # (0, ±2) corner: compressed x = 0
    rec("bls12381_p1_decompress", "80" + "00" * 47, 0)
    rec("bls12381_p1_decompress", "80" + "00" * 47, 1)
    rec("bls12381_p1_decompress", "a0" + "00" * 47, 0)
    rec("bls12381_p1_decompress", "a0" + "00" * 47, 1)
    # compressed bit clear -> not a valid compressed point
    rec("bls12381_p1_decompress", be(G1x, 48))
    # bad length
    rec("bls12381_p1_decompress", g1_comp(G1x, G1y)[:-2])

    # ---- p2_decompress --------------------------------------------------------------------
    rec("bls12381_p2_decompress", g2_comp(G2x0, G2x1, G2y0, G2y1))
    rec("bls12381_p2_decompress", g2_comp_inf())
    rec("bls12381_p2_decompress", "")
    rec("bls12381_p2_decompress", g2_comp(G2x0, G2x1, G2y0, G2y1) + g2_comp(G2x0, G2x1, G2y0, G2y1))
    rec("bls12381_p2_decompress", g2_comp(G2x0, G2x1, G2y0, G2y1)[:-2])

    # ---- map_fp_to_g1 ---------------------------------------------------------------------
    for u in [0, 1, 2, 3, 5, 11, 12345, (p - 1) // 2, p - 1]:
        rec("bls12381_map_fp_to_g1", be(u, 48))
    rec("bls12381_map_fp_to_g1", "")
    rec("bls12381_map_fp_to_g1", be(p, 48))          # non-canonical -> 1
    rec("bls12381_map_fp_to_g1", be(p + 1, 48))
    rec("bls12381_map_fp_to_g1", "ff" * 48)
    rec("bls12381_map_fp_to_g1", be(7, 48)[:-2])
    rec("bls12381_map_fp_to_g1", be(1, 48) + be(2, 48))

    # ---- map_fp2_to_g2 --------------------------------------------------------------------
    for u0, u1 in [(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (11, 13), ((p - 1) // 2, 1), (p - 1, p - 1)]:
        rec("bls12381_map_fp2_to_g2", be(u1, 48) + be(u0, 48))
    rec("bls12381_map_fp2_to_g2", "")
    rec("bls12381_map_fp2_to_g2", be(0, 48) + be(p, 48))   # c0 non-canonical -> 1
    rec("bls12381_map_fp2_to_g2", be(p, 48) + be(0, 48))   # c1 non-canonical -> 1
    rec("bls12381_map_fp2_to_g2", "ff" * 96)
    rec("bls12381_map_fp2_to_g2", be(1, 48))

    # ---- pairing_check --------------------------------------------------------------------
    rec("bls12381_pairing_check", "")                                      # empty -> 0
    rec("bls12381_pairing_check", g1gen + g2gen)                           # e(P,Q) != 1 -> 2
    rec("bls12381_pairing_check", g1_neg_enc(G1x, G1y) + g2gen)            # e(-P,Q) != 1 -> 2
    rec("bls12381_pairing_check", g1gen + g2gen + g1_neg_enc(G1x, G1y) + g2gen)  # e(P,Q)e(-P,Q) = 1 -> 0
    rec("bls12381_pairing_check", g1_inf() + g2gen)                        # e(O,Q) = 1 -> 0
    rec("bls12381_pairing_check", "00" * 288)                              # not on curve -> 1
    rec("bls12381_pairing_check", "80" + "00" * 95 + g2gen)                # top bit set -> 1
    rec("bls12381_pairing_check", ng1 + g2gen, 0)                          # not in G1 -> 1
    rec("bls12381_pairing_check", g1gen + "80" + "00" * 191)               # G2 top bit set -> 1
    rec("bls12381_pairing_check", g1gen + ng2, 0)                          # not in G2 -> 1
    rec("bls12381_pairing_check", g1gen + g2gen[:-2])                      # bad length -> err

    for host, rs in sorted(lines.items()):
        path = os.path.join(OUTDIR, host + ".jsonl")
        with open(path, "w") as f:
            for o in rs:
                f.write(json.dumps(o) + "\n")
        ok = sum(1 for o in rs if o["res"] != "err")
        print(f"{host}: {len(rs)} fixtures ({ok} non-error)")
    print("wrote", OUTDIR)

if __name__ == "__main__":
    main()
