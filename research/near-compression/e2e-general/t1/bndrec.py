#!/usr/bin/env python3
"""Python transcription of lane E's boundary record codec (`spec/lean/v3/NearSpecV3/E2E/Boundary.lean`).

`BndRec.codec`: fixed-width big-endian naturals (`natC w`), 42-B digests (`bytesC 42`), one-byte
booleans, `u64`-counted lists, a presence byte for options, fields in declaration order. `bdigest`
= the first 42 bytes of SHA-384 (U-10). Not cross-checked against a Lean evaluation (no exporter
exists for `BndRec.encode`); `selftest()` checks the round trip and widths here only.

Phase tags are `View.split`'s: init 0, eng 1, fin 2, gfin 3, done 4, doneG 5, call 6.
"""
import hashlib

DIG = 42
PHASE = {"init": 0, "eng": 1, "fin": 2, "gfin": 3, "done": 4, "doneG": 5, "call": 6}

WASM_FIELDS = [("pc", "u64"), ("sp", "u64"), ("stackRem", "u64"), ("fuel", "u64"),
               ("framesDigest", "dig"), ("memRoot", "dig"), ("memPages", "u64"),
               ("globalsDigest", "dig"), ("registersDigest", "dig"), ("vmCtxDigest", "dig"),
               ("promisesDigest", "dig"), ("codeRoot", "dig"), ("funcRoot", "dig")]

BND_FIELDS = [("claimDigest", "dig"), ("phase", "u64"), ("blockIdx", "u64"), ("receiptIdx", "u64"),
              ("actionIdx", "u64"), ("inCall", "bool"), ("t", "u64"), ("stRoot", "dig"),
              ("ctxRoot", "dig"), ("gasUsed", "u64"), ("gasBurnt", "u64"), ("balanceBurnt", "u128"),
              ("compute", "u64"), ("rPrepaid", "u64"), ("rBurnt", "u64"), ("rUsed", "u64"),
              ("outcomeAcc", "dig"), ("outRcptAcc", "diglist"), ("proposalsAcc", "dig"),
              ("bwAcc", "dig"), ("vmAcc", "dig"), ("wasm", "optwasm")]

# The digest fields: which component must produce each (plan §3.2, View.lean's table).
PRODUCER = {
    "claimDigest": "statement (wrap/INTAKE: SHA-384 of S)",
    "stRoot": "lane B (StV: working set + engine position, encStV)",
    "ctxRoot": "lane B/F (CtxV: intake record I)",
    "outcomeAcc": "lane B/G (OutV accumulators)", "outRcptAcc": "lane B/G", "proposalsAcc": "lane B/G",
    "bwAcc": "lane B/G", "vmAcc": "lane A/E (call tape K)",
    "wasm": "lane A (WmV: memRoot, ctxDigest, code/func roots)",
}


def sha384(b):
    return hashlib.sha384(b).digest()


def bdigest(b):
    return sha384(b)[:DIG]


def _nat(v, w):
    assert 0 <= v < 256 ** w, (v, w)
    return v.to_bytes(w, "big")


def _enc(kind, v):
    if kind == "u64":
        return _nat(v, 8)
    if kind == "u128":
        return _nat(v, 16)
    if kind == "dig":
        assert len(v) == DIG, len(v)
        return bytes(v)
    if kind == "bool":
        return b"\x01" if v else b"\x00"
    if kind == "diglist":
        return _nat(len(v), 8) + b"".join(_enc("dig", d) for d in v)
    if kind == "optwasm":
        if v is None:
            return b"\x00"
        return b"\x01" + b"".join(_enc(k, v[n]) for n, k in WASM_FIELDS)
    raise ValueError(kind)


def encode(rec):
    assert rec["inCall"] == (rec["wasm"] is not None), "BndRec.WF: inCall = wasm.isSome"
    return b"".join(_enc(k, rec[n]) for n, k in BND_FIELDS)


def decode(b):
    i = 0

    def take(n):
        nonlocal i
        r = b[i:i + n]
        assert len(r) == n
        i += n
        return r

    def dec(kind):
        if kind == "u64":
            return int.from_bytes(take(8), "big")
        if kind == "u128":
            return int.from_bytes(take(16), "big")
        if kind == "dig":
            return take(DIG)
        if kind == "bool":
            return take(1)[0] == 1
        if kind == "diglist":
            return [take(DIG) for _ in range(int.from_bytes(take(8), "big"))]
        if kind == "optwasm":
            if take(1)[0] == 0:
                return None
            return {n: dec(k) for n, k in WASM_FIELDS}
        raise ValueError(kind)
    r = {n: dec(k) for n, k in BND_FIELDS}
    assert i == len(b), "trailing bytes"
    return r


def digest(rec):
    """`bndOf`: the boundary digest the segment proofs would expose."""
    return bdigest(encode(rec))


ZERO = b"\x00" * DIG


def blank(claim_digest):
    """A record with every digest field at the placeholder 0^42 (no component produces it yet)."""
    r = {}
    for n, k in BND_FIELDS:
        r[n] = {"dig": ZERO, "u64": 0, "u128": 0, "bool": False, "diglist": [], "optwasm": None}[k]
    r["claimDigest"] = claim_digest
    return r


def wasm_blank():
    return {n: (ZERO if k == "dig" else 0) for n, k in WASM_FIELDS}


def to_json(rec):
    def j(v):
        if isinstance(v, (bytes, bytearray)):
            return v.hex()
        if isinstance(v, list):
            return [j(x) for x in v]
        if isinstance(v, dict):
            return {k: j(x) for k, x in v.items()}
        return v
    return j(rec)


def selftest():
    r = blank(bdigest(b"abc"))
    r.update(phase=PHASE["call"], inCall=True, wasm=wasm_blank(), gasUsed=2 ** 64 - 1, balanceBurnt=2 ** 100,
             outRcptAcc=[bdigest(b"x"), bdigest(b"y")])
    e = encode(r)
    assert decode(e) == r
    # widths: 22 fields = 7 digests*42 + 11 u64*8 + u128 16 + bool 1 + list count 8 + option byte 1
    assert len(encode(blank(ZERO))) == 7 * 42 + 11 * 8 + 16 + 1 + 8 + 1
    assert sha384(b"abc").hex().startswith("cb00753f45a35e8b")  # FIPS 180-4 / Lean `sha384_abc`
    return True


if __name__ == "__main__":
    print("bndrec selftest:", selftest())
