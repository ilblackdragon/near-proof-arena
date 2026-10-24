#!/usr/bin/env python3
"""Generate the alt_bn128 differential fixtures for the three hosts.

Two corpora, both keyed by the *pinned* oracle (`oracle/altbn128-oracle`, a verbatim transcription of
nearcore 44f7ae6c `runtime/near-vm-runner/src/logic/alt_bn128.rs` over zeropool-bn 0.5.11):

  directed  -> oracle/fixtures/v3/altbn128/<host>.jsonl
      * every vector in nearcore's own `logic/tests/alt_bn128.rs`, parsed mechanically out of the
        pinned Rust source rather than re-typed (so a transcription slip cannot hide), plus
        additional directed negatives constructed here.
  generated -> oracle/fixtures/v3/altbn128-generated/seed-<n>/<host>.jsonl
      >= 1000 comparisons per host across >= 4 seeds (acceptance contract W05 criterion 4).

Every line is `{"host", "input", "res", "out"}` where `res` is the oracle's numeric return or the
string "err" for an `AltBn128InvalidInput`/split failure, and `out` is the register hex for the two
register writers (`null` otherwise). The generator only *constructs* inputs; it never predicts an
outcome.

Run:  python3 oracle/gen_altbn128_fixtures.py [--oracle PATH] [--nearcore PATH]
"""

import argparse
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)

Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617

HOSTS = ["alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check"]
ITEM = {
    "alt_bn128_g1_multiexp": 96,
    "alt_bn128_g1_sum": 65,
    "alt_bn128_pairing_check": 192,
}

# ------------------------------------------------------------------------------------------------
# Curve arithmetic in Python, only used to *construct* candidate inputs (never to predict results).
# ------------------------------------------------------------------------------------------------


def f2mul(a, b):
    return ((a[0] * b[0] - a[1] * b[1]) % Q, (a[0] * b[1] + a[1] * b[0]) % Q)


def f2add(a, b):
    return ((a[0] + b[0]) % Q, (a[1] + b[1]) % Q)


def f2sub(a, b):
    return ((a[0] - b[0]) % Q, (a[1] - b[1]) % Q)


def f2inv(a):
    n = (a[0] * a[0] + a[1] * a[1]) % Q
    ni = pow(n, Q - 2, Q)
    return (a[0] * ni % Q, (-a[1]) % Q * ni % Q)


def g1_add(P, S):
    if P is None:
        return S
    if S is None:
        return P
    x1, y1 = P
    x2, y2 = S
    if x1 == x2 and (y1 + y2) % Q == 0:
        return None
    if P == S:
        lam = 3 * x1 * x1 % Q * pow(2 * y1, Q - 2, Q) % Q
    else:
        lam = (y2 - y1) % Q * pow((x2 - x1) % Q, Q - 2, Q) % Q
    x3 = (lam * lam - x1 - x2) % Q
    y3 = (lam * (x1 - x3) - y1) % Q
    return (x3, y3)


def g1_mul(k, P):
    A = None
    for bit in bin(k)[2:]:
        A = g1_add(A, A)
        if bit == "1":
            A = g1_add(A, P)
    return A


def g2_add(P, S):
    if P is None:
        return S
    if S is None:
        return P
    x1, y1 = P
    x2, y2 = S
    if x1 == x2 and f2add(y1, y2) == (0, 0):
        return None
    if P == S:
        num = f2mul(f2mul((3, 0), x1), x1)
        den = f2inv(f2mul((2, 0), y1))
    else:
        num = f2sub(y2, y1)
        den = f2inv(f2sub(x2, x1))
    lam = f2mul(num, den)
    x3 = f2sub(f2sub(f2mul(lam, lam), x1), x2)
    y3 = f2sub(f2mul(lam, f2sub(x1, x3)), y1)
    return (x3, y3)


def g2_mul(k, P):
    A = None
    for bit in bin(k)[2:]:
        A = g2_add(A, A)
        if bit == "1":
            A = g2_add(A, P)
    return A


# bn's G1/G2 generators (`zeropool-bn-0.5.11/src/groups/mod.rs:583-648`, de-Montgomeryised).
G1X = 1
G1Y = 2
G2X = (
    10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634,
)
G2Y = (
    8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531,
)
# The twist coefficient b' = 3/(9+i) (`G2Params::coeff_b`).
G2B = (
    19485874751759354771024239261021720505790618469301721065564631296452457478373,
    266929791119991161246907387137283842545076965332900288569378510910307636690,
)


def le32(x):
    return int(x % Q).to_bytes(32, "little")


def g1_bytes(P):
    """64-byte little-endian G1 encoding; `None` (infinity) is 64 zero bytes."""
    if P is None:
        return b"\x00" * 64
    return le32(P[0]) + le32(P[1])


def g2_bytes(P):
    """128-byte little-endian G2 encoding, `x.real ‖ x.imag ‖ y.real ‖ y.imag`."""
    if P is None:
        return b"\x00" * 128
    (xr, xi), (yr, yi) = P
    return le32(xr) + le32(xi) + le32(yr) + le32(yi)


def g1_on_curve(P):
    if P is None:
        return True
    x, y = P
    return y * y % Q == (x * x * x + 3) % Q


def g2_on_curve(P):
    if P is None:
        return True
    X, Y = P
    return f2mul(Y, Y) == f2add(f2mul(f2mul(X, X), X), G2B)


# ------------------------------------------------------------------------------------------------
# Oracle wrapper
# ------------------------------------------------------------------------------------------------


def oracle(binary, host, data):
    r = subprocess.run([binary, host, data.hex()], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"oracle failed: {r.stderr.strip()}")
    lines = r.stdout.strip().splitlines()
    res = "err"
    out = None
    for ln in lines:
        if ln.startswith("res "):
            v = ln[4:].strip()
            res = "err" if v == "err" else int(v)
        elif ln.startswith("out "):
            out = ln[4:].strip()
    if res == "err":
        out = None
    return {"host": host, "input": data.hex(), "res": res, "out": out}


# ------------------------------------------------------------------------------------------------
# 1. Directed corpus: nearcore's own vectors, parsed from the pinned Rust source
# ------------------------------------------------------------------------------------------------

# The test bodies in `logic/tests/alt_bn128.rs` are `check_ok(&le_bytes![...], ...)` /
# `check_err(&le_bytes![...], "msg")` calls. Rather than re-type the constants, extract each
# `le_bytes![...]` token list in file order and group them by the enclosing test function.

TEST_FN = re.compile(r"fn (test_alt_bn128_\w+)\(\)")
LE_BYTES = re.compile(r"le_bytes!\[([^\]]*)\]", re.S)
BYTE_LIT = re.compile(r"^(\d+)u8$")


def parse_le_bytes(body):
    """`le_bytes!` semantics: each `0x..` literal is a u256 written little-endian; each `Nu8` is one
    raw byte. Commas are separators only."""
    out = bytearray()
    for tok in re.split(r"[,\s]+", body):
        tok = tok.strip()
        if not tok:
            continue
        m = BYTE_LIT.match(tok)
        if m:
            out.append(int(m.group(1)) & 0xFF)
            continue
        v = int(tok, 16)
        # u128::from_le_bytes(lo) ‖ u128::from_le_bytes(hi), lo = low 32 hex digits
        out += v.to_bytes(32, "little")
    return bytes(out)


def directed_from_nearcore(nearcore):
    path = os.path.join(
        nearcore, "runtime/near-vm-runner/src/logic/tests/alt_bn128.rs"
    )
    src = open(path).read()
    # split into test functions
    marks = [(m.start(), m.group(1)) for m in TEST_FN.finditer(src)]
    results = {h: [] for h in HOSTS}
    name_of = {
        "test_alt_bn128_g1_multiexp": "alt_bn128_g1_multiexp",
        "test_alt_bn128_g1_sum": "alt_bn128_g1_sum",
        "test_alt_bn128_pairing_check": "alt_bn128_pairing_check",
    }
    for i, (start, fn) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(src)
        chunk = src[start:end]
        host = name_of.get(fn)
        if host is None:
            continue
        # every le_bytes![...] literal in this function, in order. For check_ok(input, expected)
        # pairs the first is the input and the second the expected output; for check_err the sole
        # literal is the input. Both reduce to "all literals in order" plus the kind of the call.
        for m in LE_BYTES.finditer(chunk):
            results[host].append(parse_le_bytes(m.group(1)))
    return results


def _split_top_level_args(call_body):
    """Split `call_body` at commas that sit outside every `()`, `[]`, `{}` group."""
    parts, cur = [], []
    depth = 0
    i = 0
    while i < len(call_body):
        c = call_body[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                break
            depth -= 1
        if c == ',' and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(c)
        i += 1
    parts.append("".join(cur))
    return [p.strip() for p in parts]


def _parse_input_literal(arg):
    """The first argument of a `check_*` call, as bytes."""
    m = LE_BYTES.search(arg)
    if m:
        return parse_le_bytes(m.group(1))
    raw = re.search(r"&\[([0-9,\s]*)\]", arg)
    if raw:
        return bytes(int(x) for x in raw.group(1).split(",") if x.strip())
    bytestr = re.search(r'b"([^"]*)"', arg)
    if bytestr:
        return bytestr.group(1).encode()
    return None


def directed_cases(nearcore):
    """Return per-host lists of `(input, expected)` where `expected` is either `("ok", bytes)` for a
    `check_ok(input, expected_output)` call or `("err", msg_fragment)` for `check_err`.

    The expected values are parsed out of nearcore's own test bodies, so the oracle run can be
    asserted against nearcore's asserted verdicts — not only against itself."""
    path = os.path.join(nearcore, "runtime/near-vm-runner/src/logic/tests/alt_bn128.rs")
    src = open(path).read()
    marks = [(m.start(), m.group(1)) for m in TEST_FN.finditer(src)]
    name_of = {
        "test_alt_bn128_g1_multiexp": "alt_bn128_g1_multiexp",
        "test_alt_bn128_g1_sum": "alt_bn128_g1_sum",
        "test_alt_bn128_pairing_check": "alt_bn128_pairing_check",
    }
    CALL = re.compile(r"check_(ok|err)\s*\(")
    out = {h: [] for h in HOSTS}
    for i, (start, fn) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(src)
        chunk = src[start:end]
        host = name_of.get(fn)
        if host is None:
            continue
        for cm in CALL.finditer(chunk):
            args = _split_top_level_args(chunk[cm.end():])
            if not args:
                continue
            data = _parse_input_literal(args[0])
            if data is None:
                continue
            kind = cm.group(1)
            if kind == "err":
                msg = re.search(r'"([^"]*)"', args[1]).group(1) if len(args) > 1 else ""
                out[host].append((data, ("err", msg)))
            elif host == "alt_bn128_pairing_check":
                # check_ok(input, 0|1)
                out[host].append((data, ("ok", args[1].strip())))
            else:
                exp = _parse_input_literal(args[1]) if len(args) > 1 else None
                out[host].append((data, ("ok", exp)))
    return out


# ------------------------------------------------------------------------------------------------
# 2. Additional directed negatives (constructed here, verdicts from the oracle)
# ------------------------------------------------------------------------------------------------


def directed_extra():
    extra = {h: [] for h in HOSTS}
    # --- g1_multiexp ---
    g1m = extra["alt_bn128_g1_multiexp"]
    g1m.append((b"", "ok"))  # empty -> infinity
    g1m.append((b"X" * 95, "err"))  # not a multiple of 96
    g1m.append((b"X" * 97, "err"))
    g1m.append((g1_bytes((G1X, G1Y)) + le32(0), "ok"))  # 0 * G = infinity
    g1m.append((g1_bytes((G1X, G1Y)) + le32(R), "err"))  # scalar == r is not canonical
    g1m.append((g1_bytes((G1X, G1Y)) + le32(R - 1), "ok"))  # r-1 is canonical
    g1m.append((g1_bytes((G1X, G1Y)) + le32(Q), "err"))  # Q >= r too
    g1m.append((g1_bytes((G1X, G1Y + 1)) + le32(1), "err"))  # off-curve y
    g1m.append((g1_bytes((2, 3)) + le32(1), "err"))  # (2,3) not on y^2=x^3+3? 9 != 11
    g1m.append((b"\x00" * 64 + le32(1), "ok"))  # infinity input, scalar 1
    g1m.append((g1_bytes((G1X, G1Y)) + b"\xff" * 32, "err"))  # scalar all-ones
    g1m.append((le32(Q) + le32(0) + le32(1), "err"))  # x noncanonical
    # --- g1_sum ---
    g1s = extra["alt_bn128_g1_sum"]
    g1s.append((b"", "ok"))
    g1s.append((b"\x00" * 65, "ok"))  # sign 0 + infinity
    g1s.append((b"\x01" + b"\x00" * 64, "ok"))  # sign 1 + infinity
    g1s.append((b"\x02" + b"\x00" * 64, "err"))  # bad sign
    g1s.append((b"\xff" + b"\x00" * 64, "err"))
    g1s.append((b"\x00" * 64, "err"))  # 64 bytes is not a multiple of 65
    g1s.append((b"\x00" + g1_bytes((G1X, G1Y)), "ok"))
    g1s.append((b"\x01" + g1_bytes((G1X, G1Y)), "ok"))  # -G
    g1s.append(
        (b"\x00" + g1_bytes((G1X, G1Y)) + b"\x01" + g1_bytes((G1X, G1Y)), "ok")
    )  # G - G = infinity
    g1s.append((b"\x00" + le32(Q) + le32(0), "err"))  # noncanonical x
    g1s.append((b"\x00" + g1_bytes((G1X, G1Y + 1)), "err"))  # off-curve
    # --- pairing_check ---
    pc = extra["alt_bn128_pairing_check"]
    pc.append((b"", "ok"))
    pc.append((b"X" * 191, "err"))
    pc.append((b"X" * 193, "err"))
    pc.append((g1_bytes(None) + g2_bytes(None), "ok"))  # infinity pair contributes 1
    pc.append((g1_bytes((G1X, G1Y)) + g2_bytes(None), "ok"))
    pc.append((g1_bytes(None) + g2_bytes((G2X, G2Y)), "ok"))
    pc.append((g1_bytes((G1X, G1Y)) + g2_bytes((G2X, G2Y)), "ok"))  # nondegenerate, product != 1
    pc.append((g1_bytes((G1X, G1Y)) + g2_bytes((G2X, G2Y)) + g1_bytes((G1X, G1Y)) + g2_bytes((G2X, G2Y)), "ok"))
    # e(G,G) * e(-G,G) = 1
    negG = (G1X, (Q - G1Y) % Q)
    pc.append((g1_bytes((G1X, G1Y)) + g2_bytes((G2X, G2Y)) + g1_bytes(negG) + g2_bytes((G2X, G2Y)), "ok"))
    # e(2G,G) * e(-G,2G) = 1
    g2d = g2_mul(2, (G2X, G2Y))
    pc.append((g1_bytes(g1_mul(2, (G1X, G1Y))) + g2_bytes((G2X, G2Y)) + g1_bytes(negG) + g2_bytes(g2d), "ok"))
    # G2 subgroup failure: an on-twist point outside G2. Take G2 generator's x, y = -y_gen.
    # (on twist but not in the order-r subgroup only for non-generator points; use a twist point
    # of small order by scaling with a non-r multiple is hard, so use x noncanonical instead.)
    pc.append((g1_bytes((G1X, G1Y)) + le32(Q) + le32(0) + le32(0) + le32(0), "err"))  # noncanonical g2 x
    pc.append((g1_bytes((G1X, G1Y)) + g2_bytes((G2X, (G2Y[0], (G2Y[1] + 1) % Q))), "err"))  # off-twist
    pc.append((g1_bytes((G1X, G1Y + 1)) + g2_bytes((G2X, G2Y)), "err"))  # off-curve g1
    pc.append((le32(Q) + le32(0) + g2_bytes((G2X, G2Y)), "err"))  # noncanonical g1 x
    return extra


# ------------------------------------------------------------------------------------------------
# 3. Generated corpus
# ------------------------------------------------------------------------------------------------


def rnd_scalar(rng):
    return rng.randrange(R)


def rnd_g1(rng):
    """Random element of G1 = [k]·G, as an affine point."""
    k = rnd_scalar(rng)
    if k == 0:
        k = 1
    return g1_mul(k, (G1X, G1Y))


def rnd_g2(rng):
    k = rnd_scalar(rng)
    if k == 0:
        k = 1
    return g2_mul(k, (G2X, G2Y))


def noncanonical_fq(rng):
    return (Q + rng.randrange(1, 2**32)).to_bytes(32, "little")


def generated_case(rng, host, kind):
    """Build one candidate input of the requested kind for `host`."""
    if host == "alt_bn128_g1_multiexp":
        n = rng.randrange(0, 4)
        body = bytearray()
        for _ in range(n):
            P = rnd_g1(rng)
            body += g1_bytes(P)
            if kind == "noncanonical_scalar":
                body += (R + rng.randrange(0, 2**16)).to_bytes(32, "little")
            elif kind == "noncanonical_point":
                body += noncanonical_fq(rng)
            else:
                body += le32(rnd_scalar(rng))
        if kind == "offcurve":
            P = rnd_g1(rng)
            body = bytearray(g1_bytes((P[0], (P[1] + 1) % Q)) + le32(1))
        if kind == "infinity":
            body = bytearray(b"\x00" * 64 + le32(rng.randrange(0, 2**64)))
        if kind == "wrong_len":
            body = bytearray(bytes(rng.randrange(256) for _ in range(rng.choice([1, 95, 97, 191]))))
        return bytes(body)
    if host == "alt_bn128_g1_sum":
        n = rng.randrange(0, 4)
        body = bytearray()
        for _ in range(n):
            P = rnd_g1(rng)
            sign = rng.choice([0, 1])
            body += bytes([sign]) + g1_bytes(P)
            if kind == "badsign":
                body = bytearray(bytes([rng.choice([2, 3, 92, 255])]) + g1_bytes(P))
        if kind == "offcurve":
            P = rnd_g1(rng)
            body = bytearray(b"\x00" + g1_bytes((P[0], (P[1] + 1) % Q)))
        if kind == "noncanonical_point":
            body = bytearray(b"\x00" + noncanonical_fq(rng) + le32(0))
        if kind == "infinity":
            body = bytearray(b"\x00" + b"\x00" * 64)
        if kind == "wrong_len":
            body = bytearray(bytes(rng.randrange(256) for _ in range(rng.choice([1, 64, 66, 130]))))
        return bytes(body)
    # pairing_check
    n = rng.randrange(0, 3)
    body = bytearray()
    for _ in range(n):
        P = rnd_g1(rng)
        S = rnd_g2(rng)
        body += g1_bytes(P) + g2_bytes(S)
    if kind == "cancelling":
        # e(G, S) * e(-G, S) = 1
        P = rnd_g1(rng)
        S = rnd_g2(rng)
        negP = (P[0], (Q - P[1]) % Q)
        body = bytearray(g1_bytes(P) + g2_bytes(S) + g1_bytes(negP) + g2_bytes(S))
    if kind == "offcurve":
        P = rnd_g1(rng)
        S = rnd_g2(rng)
        body = bytearray(g1_bytes((P[0], (P[1] + 1) % Q)) + g2_bytes(S))
    if kind == "noncanonical_point":
        S = rnd_g2(rng)
        body = bytearray(noncanonical_fq(rng) + le32(0) + g2_bytes(S))
    if kind == "infinity":
        body = bytearray(g1_bytes(None) + g2_bytes(None))
    if kind == "wrong_len":
        body = bytearray(bytes(rng.randrange(256) for _ in range(rng.choice([1, 191, 193, 383]))))
    return bytes(body)


KINDS = [
    "plain",
    "plain",
    "plain",
    "infinity",
    "offcurve",
    "noncanonical_scalar",
    "noncanonical_point",
    "wrong_len",
    "cancelling",
    "badsign",
]

SEEDS = [20261023, 20261024, 20261025, 20261026]
PER_HOST = 260  # x 4 seeds = 1040 generated comparisons per host


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--oracle",
        default=os.path.join(HERE, "altbn128-oracle", "target", "release", "altbn128-oracle"),
    )
    ap.add_argument("--nearcore", default="/data/illia/nearproof-deps/nearcore")
    ap.add_argument("--skip-generated", action="store_true")
    args = ap.parse_args()

    if not os.path.exists(args.oracle):
        sys.exit(f"oracle not built: {args.oracle} (cargo build --release --offline there)")

    # --- directed ---
    directed = directed_cases(args.nearcore)
    extra = directed_extra()
    outdir = os.path.join(HERE, "fixtures", "v3", "altbn128")
    os.makedirs(outdir, exist_ok=True)
    summary = {}
    for host in HOSTS:
        lines = []
        for data, _kind in directed.get(host, []) + extra[host]:
            lines.append(oracle(args.oracle, host, data))
        path = os.path.join(outdir, host + ".jsonl")
        with open(path, "w") as f:
            for ln in lines:
                f.write(json.dumps(ln) + "\n")
        summary[host] = len(lines)
        ok = sum(1 for x in lines if x["res"] != "err")
        print(f"directed {host}: {len(lines)} rows ({ok} accept, {len(lines)-ok} error)")

    if args.skip_generated:
        return

    # --- generated ---
    for seed in SEEDS:
        rng = random.Random(seed)
        seeddir = os.path.join(HERE, "fixtures", "v3", "altbn128-generated", f"seed-{seed}")
        os.makedirs(seeddir, exist_ok=True)
        for host in HOSTS:
            lines = []
            for i in range(PER_HOST):
                kind = KINDS[i % len(KINDS)]
                data = generated_case(rng, host, kind)
                lines.append(oracle(args.oracle, host, data))
            path = os.path.join(seeddir, host + ".jsonl")
            with open(path, "w") as f:
                for ln in lines:
                    f.write(json.dumps(ln) + "\n")
        print(f"generated seed-{seed}: {PER_HOST} rows x {len(HOSTS)} hosts")


if __name__ == "__main__":
    main()
