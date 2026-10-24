#!/usr/bin/env python3
"""Generate the *generated-coverage* BLS12-381 differential fixtures.

Acceptance contract W05 criterion 4 asks for >= 1,000 generated comparisons per semantic family
across >= 4 recorded seeds. The directed fixtures in `gen_bls_fixtures.py` are not enough, so this
script produces a second corpus under `oracle/fixtures/v3/bls12381-generated/seed-<n>/`.

Every fixture line is the oracle's own verdict (`bls-oracle <host> <hex> <version>`), i.e. nearcore
44f7ae6c `runtime/near-vm-runner/src/logic/bls12381.rs` over blst 0.3.11. The generator only
*constructs* inputs (valid points via the pinned generators plus scalar multiplication, and
deliberate malformations); it never predicts an outcome.

Input classes per host, mixed so both the accept and the reject branches are exercised:
  * valid encodings (generator, random subgroup elements, scaled copies)
  * infinity encodings
  * non-canonical Fp coordinates (x >= p)
  * off-curve coordinates
  * subgroup failures (on-curve, outside G1/G2)
  * wrong lengths (the `err` branch of `check_input_size`)
  * corrupted flag bits (top bit set / compressed bit clear / sign bit flipped)
  * truncated elements and random bytes

Output: one JSON object per line,
`{"host": ..., "input": "<hex>", "version": 0, "res": <u64|"err">, "out": "<hex>"|null}`.
"""
import json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gen_bls_fixtures as g  # reuse the point constructors and the oracle wrapper

OUTROOT = os.path.join(HERE, "fixtures", "v3", "bls12381-generated")
SEEDS = [20261023, 20261024, 20261025, 20261026]
PER_HOST = 260  # x 4 seeds = 1040 generated comparisons per host


def be(x, n):
    return g.be(x, n)


def rnd_fp(rng):
    return rng.randrange(g.p)


def rnd_scalar(rng):
    return rng.randrange(g.r)


def noncanonical_fp(rng):
    """An Fp encoding whose value is >= p (so blst's canonical round-trip check rejects it)."""
    return be(g.p + rng.randrange(1, 2**64), 48)


def g1_random(rng):
    """A random element of G1: a random scalar times the generator, as an uncompressed encoding."""
    k = rnd_scalar(rng)
    x, y = g._g1_mul(k, (g.G1x, g.G1y))
    return g.g1_unc(x, y), x, y


def g2_random(rng):
    """A random element of G2."""
    k = rnd_scalar(rng)
    P = g._g2_mul(k, ((g.G2x0, g.G2x1), (g.G2y0, g.G2y1)))
    (x0, x1), (y0, y1) = P
    return g.g2_unc(x0, x1, y0, y1)


def g1_offcurve(rng):
    """`(x, y)` with `y^2 != x^3 + 4`."""
    x = rnd_fp(rng)
    rhs = (pow(x, 3, g.p) + 4) % g.p
    y = rnd_fp(rng)
    while (y * y) % g.p == rhs:
        y = rnd_fp(rng)
    return g.g1_unc(x, y)


def g2_offcurve(rng):
    x0, x1 = rnd_fp(rng), rnd_fp(rng)
    y0, y1 = rnd_fp(rng), rnd_fp(rng)
    # the twist's b coefficient is 4(u+1) = 4 + 4u
    rhs0 = (pow(x0, 3, g.p) - 3 * x0 * x1 * x1 + 4) % g.p
    rhs1 = (3 * x0 * x0 * x1 - pow(x1, 3, g.p) + 4) % g.p
    lhs0 = (y0 * y0 - y1 * y1) % g.p
    lhs1 = (2 * y0 * y1) % g.p
    while lhs0 == rhs0 and lhs1 == rhs1:
        y0, y1 = rnd_fp(rng), rnd_fp(rng)
        lhs0 = (y0 * y0 - y1 * y1) % g.p
        lhs1 = (2 * y0 * y1) % g.p
    return g.g2_unc(x0, x1, y0, y1)


def _mutate(rng, enc, width):
    """Apply one structural malformation to a `width`-byte G1/G2 encoding."""
    b = bytearray.fromhex(enc)
    n = len(b)
    kind = rng.randrange(7)
    if kind == 0:                       # top bit set -> not a valid uncompressed point
        b[0] |= 0x80
    elif kind == 1:                     # infinity flag without zero payload
        b[0] |= 0x40
        b[rng.randrange(1, n)] = rng.randrange(1, 256)
    elif kind == 2:                     # corrupt one byte
        b[rng.randrange(n)] ^= 1 << rng.randrange(8)
    elif kind == 3:                     # truncate
        return bytes(b[:max(1, rng.randrange(1, n))]).hex()
    elif kind == 4:                     # append garbage
        return (bytes(b) + bytes(rng.randrange(1, 40))).hex()
    elif kind == 5:                     # non-canonical x
        b[0:48] = bytes.fromhex(noncanonical_fp(rng))
    else:                               # all zeros
        return "00" * width
    return bytes(b).hex()


def g1_mutate(rng, enc):
    """Apply one structural malformation to a G1 encoding of whatever width it arrives in."""
    return _mutate(rng, enc, len(enc) // 2)


def g2_mutate(rng, enc):
    """Apply one structural malformation to a G2 encoding of whatever width it arrives in."""
    return _mutate(rng, enc, len(enc) // 2)


def g1_compress_enc(rng, x, y):
    return g.g1_comp(x, y)


def g2_compress_enc(rng, enc):
    """Compress a 192-byte uncompressed G2 encoding produced by `g2_random`."""
    b = bytes.fromhex(enc)
    x1 = int.from_bytes(b[0:48], "big")
    x0 = int.from_bytes(b[48:96], "big")
    y1 = int.from_bytes(b[96:144], "big")
    return g.g2_comp(x0, x1, y1, int.from_bytes(b[144:192], "big"))


def gen_host(rng, host):
    """Return one generated input (hex) for `host`."""
    if host == "bls12381_p1_sum":
        kind = rng.randrange(10)
        if kind <= 3:
            enc, _, _ = g1_random(rng)
            return f"{rng.randrange(2):02x}" + enc
        if kind == 4:
            return "00" + g.g1_inf()
        if kind == 5:
            return "00" + g1_offcurve(rng)
        if kind == 6:
            return f"{rng.randrange(2):02x}" + g.g1_not_in_group()
        if kind == 7:
            n = rng.randrange(0, 4)
            return "".join(f"{rng.randrange(2):02x}" + g1_random(rng)[0] for _ in range(n))
        if kind == 8:
            return "00" + g1_mutate(rng, g.g1_unc(g.G1x, g.G1y))
        return f"{rng.randrange(2):02x}" + g1_random(rng)[0][: rng.randrange(1, 97) * 2]

    if host == "bls12381_p2_sum":
        kind = rng.randrange(9)
        if kind <= 3:
            return f"{rng.randrange(2):02x}" + g2_random(rng)
        if kind == 4:
            return "00" + g.g2_inf()
        if kind == 5:
            return "00" + g2_offcurve(rng)
        if kind == 6:
            return f"{rng.randrange(2):02x}" + g.g2_not_in_group()
        if kind == 7:
            n = rng.randrange(0, 3)
            return "".join(f"{rng.randrange(2):02x}" + g2_random(rng) for _ in range(n))
        return "00" + g2_mutate(rng, g.g2_unc(g.G2x0, g.G2x1, g.G2y0, g.G2y1))

    if host == "bls12381_g1_multiexp":
        kind = rng.randrange(8)
        if kind <= 3:
            enc, _, _ = g1_random(rng)
            return enc + g.le32(rnd_scalar(rng))
        if kind == 4:
            return g.g1_unc(g.G1x, g.G1y) + g.le32(2**rng.randrange(0, 256))
        if kind == 5:
            return g.g1_not_in_group() + g.le32(rnd_scalar(rng))
        if kind == 6:
            n = rng.randrange(0, 3)
            return "".join(g1_random(rng)[0] + g.le32(rnd_scalar(rng)) for _ in range(n))
        return g1_mutate(rng, g.g1_unc(g.G1x, g.G1y)) + g.le32(rnd_scalar(rng))

    if host == "bls12381_g2_multiexp":
        kind = rng.randrange(7)
        if kind <= 3:
            return g2_random(rng) + g.le32(rnd_scalar(rng))
        if kind == 4:
            return g.g2_not_in_group() + g.le32(rnd_scalar(rng))
        if kind == 5:
            n = rng.randrange(0, 2)
            return "".join(g2_random(rng) + g.le32(rnd_scalar(rng)) for _ in range(n))
        return g2_mutate(rng, g.g2_unc(g.G2x0, g.G2x1, g.G2y0, g.G2y1)) + g.le32(rnd_scalar(rng))

    if host == "bls12381_p1_decompress":
        kind = rng.randrange(9)
        if kind <= 3:
            _, x, y = g1_random(rng)
            return g1_compress_enc(rng, x, y)
        if kind == 4:
            return g.g1_comp_inf()
        if kind == 5:
            # compressed infinity with a sign bit set
            return "e0" + "00" * 47
        if kind == 6:
            return g1_mutate(rng, g1_compress_enc(rng, g.G1x, g.G1y))
        if kind == 7:
            n = rng.randrange(0, 3)
            return "".join(g1_compress_enc(rng, *g1_random(rng)[1:]) for _ in range(n))
        # compressed bit clear
        return be(rnd_fp(rng), 48)

    if host == "bls12381_p2_decompress":
        kind = rng.randrange(7)
        if kind <= 3:
            return g2_compress_enc(rng, g2_random(rng))
        if kind == 4:
            return g.g2_comp_inf()
        if kind == 5:
            n = rng.randrange(0, 2)
            return "".join(g2_compress_enc(rng, g2_random(rng)) for _ in range(n))
        return g2_mutate(rng, g2_compress_enc(rng, g.g2_unc(g.G2x0, g.G2x1, g.G2y0, g.G2y1)))

    if host == "bls12381_map_fp_to_g1":
        kind = rng.randrange(7)
        if kind <= 4:
            return be(rnd_fp(rng), 48)
        if kind == 5:
            n = rng.randrange(0, 3)
            return "".join(be(rnd_fp(rng), 48) for _ in range(n))
        return g1_mutate(rng, be(rnd_fp(rng), 48))

    if host == "bls12381_map_fp2_to_g2":
        kind = rng.randrange(7)
        if kind <= 4:
            return be(rnd_fp(rng), 48) + be(rnd_fp(rng), 48)
        if kind == 5:
            n = rng.randrange(0, 2)
            return "".join(be(rnd_fp(rng), 48) + be(rnd_fp(rng), 48) for _ in range(n))
        return g2_mutate(rng, be(rnd_fp(rng), 48) + be(rnd_fp(rng), 48))

    if host == "bls12381_pairing_check":
        kind = rng.randrange(10)
        if kind <= 3:
            # e(P,Q) * e(-P,Q) = 1 with a random subgroup P
            enc, x, y = g1_random(rng)
            q = g2_random(rng)
            neg = g.g1_unc(x, g.neg_y(y))
            return enc + q + neg + q
        if kind == 4:
            enc, _, _ = g1_random(rng)
            return enc + g2_random(rng)
        if kind == 5:
            return g.g1_inf() + g2_random(rng)
        if kind == 6:
            return g1_random(rng)[0] + g.g2_inf()
        if kind == 7:
            return g.g1_not_in_group() + g2_random(rng)
        if kind == 8:
            return g1_random(rng)[0] + g.g2_not_in_group()
        # malformed / wrong length
        return g1_mutate(rng, g.g1_unc(g.G1x, g.G1y)) + g2_random(rng)

    raise SystemExit(f"unknown host {host}")


HOSTS = [
    "bls12381_p1_sum", "bls12381_p2_sum",
    "bls12381_g1_multiexp", "bls12381_g2_multiexp",
    "bls12381_p1_decompress", "bls12381_p2_decompress",
    "bls12381_map_fp_to_g1", "bls12381_map_fp2_to_g2",
    "bls12381_pairing_check",
]


def main():
    total = 0
    for seed in SEEDS:
        rng = random.Random(seed)
        outdir = os.path.join(OUTROOT, f"seed-{seed}")
        os.makedirs(outdir, exist_ok=True)
        for host in HOSTS:
            rows = []
            seen = set()
            tries = 0
            while len(rows) < PER_HOST and tries < PER_HOST * 40:
                tries += 1
                inp = gen_host(rng, host)
                if inp in seen:
                    continue
                seen.add(inp)
                res, out = g.ask(host, inp, 0)
                rows.append({"host": host, "input": inp, "version": 0, "res": res, "out": out})
            with open(os.path.join(outdir, host + ".jsonl"), "w") as f:
                for o in rows:
                    f.write(json.dumps(o) + "\n")
            total += len(rows)
        print(f"seed {seed}: wrote {sum(PER_HOST for _ in HOSTS)} rows under {outdir}")
    print(f"total generated fixtures: {total}")


if __name__ == "__main__":
    main()
