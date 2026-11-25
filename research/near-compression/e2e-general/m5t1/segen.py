#!/usr/bin/env python3
"""F-5: the STATE engine half's leaf dump (`SE`, `M5T1/Se.lean`) for one STATE leaf of lane I's chain.

  segen.py CHAIN.json LEAF OUT_DIR [--template T.json] [--mutant NAME]

LEAF is a leaf name of the chain's leaf table (`STATE seg A` = c1 → c2, `STATE seg B` = c7 → c8,
`finalize` = c8 → c9). The public values are the two cut records, `BndRec.encode` bytes (`engF`,
450 B each), taken from the chain unchanged; `SE` row 0 holds the `STMQ`/`STMA` metas (stand-ins:
`tag` = the `stRoot` commitment's tag of the record — `1` at a non-final position, `3` at `done` —
and `rest = 0^42`, lane E's `encRestI` not adopted); `RNG` counts the meta bytes; `XTAPE` is the T1
stand-in for lane B's `STC` (consumes `STMQ` with the input `stRoot`, answers `STMA` with the
output's). The engine half's rules (`Se.seRule`) are asserted on the pair before writing.

Mutants (each must be rejected by the leaf): `phase` (B_out phase 6), `vmacc` (B_out vmAcc not
`bdigest []`), `prepaid` (B_out rPrepaid 1), `gasburnt` (B_out gasBurnt ≠ gasUsed), `ctxcopy`
(B_out ctxRoot changed), `claimcopy` (B_out claimDigest changed), `clock` (B_out t = 1),
`incall` (B_in a call record's inCall byte), `stroot` (B_out stRoot ≠ the STC answer); F-6: `nonbyte` (claimDigest byte 0 of both records + 256).
"""
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rtbnd  # noqa: E402

bndrec = rtbnd.bndrec
P = 0x78000001
B_RNG, B_STMQ, B_STMA = 2, 17, 18
SE_NAMES = ["tgo"] + [f"rso.{j}" for j in range(42)] + ["tgi"] + [f"rsi.{j}" for j in range(42)]
COPY = ["claimDigest", "blockIdx", "actionIdx", "t", "ctxRoot", "bwAcc"]
STATE_LEAVES = ("STATE seg A", "STATE seg B", "finalize")


def limb3(b):
    return [(b[3 * j] << 16) | (b[3 * j + 1] << 8) | b[3 * j + 2] for j in range(14)]


def pair(ch, leaf):
    lv = {x["leaf"]: (int(x["in"][1:]), int(x["out"][1:])) for x in ch["leaves"]}
    assert leaf in STATE_LEAVES and leaf in lv, f"{leaf}: not a STATE leaf of the chain"
    a, b = lv[leaf]
    b_in, b_out = rtbnd.from_json(ch["cuts"][a]), rtbnd.from_json(ch["cuts"][b])
    return a, b, b_in, b_out


def check_rules(b_in, b_out):
    """`Se.seRule` on the records (what the leaf's constraints say)."""
    assert b_in["phase"] == 1 and not b_in["inCall"] and b_in["wasm"] is None, "input: engine record"
    assert b_out["phase"] == 1 and not b_out["inCall"] and b_out["wasm"] is None, "output: engine record"
    assert b_out["vmAcc"] == rtbnd.EMPTY, "vmAcc = bdigest []"
    assert b_out["rPrepaid"] == b_out["rBurnt"] == b_out["rUsed"] == 0, "clear: rPrepaid/rBurnt/rUsed = 0"
    assert b_out["gasUsed"] == b_out["gasBurnt"], "clear: gasUsed = gasBurnt"
    assert len(b_in["outRcptAcc"]) == len(b_out["outRcptAcc"]) == 1, "singleton outRcptAcc"
    for f in COPY:
        assert b_in[f] == b_out[f], f"copied: {f}"


def st_tag(rec, ch, cut):
    """The `stRoot` commitment's tag at a cut: lane I's chain builds `StCommit.ser` with tag 1 at a
    non-final engine position and 3 at `eng I ⟨done out⟩` (lane B's `tagOf`)."""
    return 3 if cut == 9 else 1


def main():
    a = sys.argv[1:]
    opt = {}
    for k in ("--template", "--mutant"):
        if k in a:
            i = a.index(k)
            opt[k] = a[i + 1]
            a = a[:i] + a[i + 2:]
    chain_path, leaf, out = a
    ch = json.load(open(chain_path))
    ca, cb, b_in, b_out = pair(ch, leaf)
    check_rules(b_in, b_out)
    d_in, d_out = bndrec.digest(b_in).hex(), bndrec.digest(b_out).hex()
    assert (d_in, d_out) == (ch["digests"][ca], ch["digests"][cb]), "digests = the chain's"
    h_out = dict(b_out)                 # the honest output: the stand-in STC answers its stRoot
    m = opt.get("--mutant")
    if m:
        r, ri = dict(b_out), dict(b_in)
        if m == "phase":
            r["phase"] = 6
        elif m == "vmacc":
            r["vmAcc"] = bndrec.bdigest(b"vm")
        elif m == "prepaid":
            r["rPrepaid"] = 1
        elif m == "gasburnt":
            r["gasBurnt"] = r["gasUsed"] + 1
        elif m == "ctxcopy":
            r["ctxRoot"] = bytes([r["ctxRoot"][0] ^ 1]) + r["ctxRoot"][1:]
        elif m == "claimcopy":
            r["claimDigest"] = bytes([r["claimDigest"][0] ^ 1]) + r["claimDigest"][1:]
        elif m == "clock":
            r["t"] = 1
        elif m == "incall":
            ri["inCall"] = True
        elif m == "stroot":
            r["stRoot"] = bytes([r["stRoot"][0] ^ 1]) + r["stRoot"][1:]
        elif m == "nonbyte":
            pass
        else:
            raise SystemExit(f"unknown mutant {m}")
        b_in, b_out = ri, r
        print(f"mutant applied: [{m}]")
    e_in = bndrec.encode(b_in) if not (m == "incall") else bndrec.encode(dict(b_in, inCall=False))
    if m == "incall":
        # the inCall byte of an engine record flipped to 1 (the record no longer decodes as WF)
        e_in = bytearray(e_in)
        e_in[42 + 8 * 4] = 1
        e_in = bytes(e_in)
    e_out = bndrec.encode(b_out)
    assert len(e_in) == 450 and len(e_out) == 450
    pubs = list(e_in) + list(e_out)
    if m == "nonbyte":
        # F-6: claimDigest byte 0 of both records + 256 (copied: the copy holds; not a byte)
        pubs[0] += 256
        pubs[450] += 256
    os.makedirs(out, exist_ok=True)
    tgo, tgi = st_tag(h_out, ch, cb), st_tag(b_in, ch, ca)
    rso, rsi = [0] * 42, [0] * 42       # stand-in metas: rest = 0^42 (encRestI not adopted)
    row = [tgo] + rso + [tgi] + rsi
    rng = [0] * 256
    for v in rso + rsi + pubs:          # F-6: + every public value (`Ids.pubBytes`)
        if v < 256:
            rng[v] += 1
    with open(f"{out}/SE.bin", "wb") as f:
        f.write(struct.pack("<II", 2, len(SE_NAMES)))
        cells = row + [0] * (3 * len(SE_NAMES))
        f.write(struct.pack(f"<{len(cells)}I", *cells))
    with open(f"{out}/RNG.bin", "wb") as f:
        f.write(struct.pack("<II", 8, 21))
        cells = []
        for v in range(256):
            cells += [v] + [(rng[v] >> t) & 1 for t in range(20)]
        f.write(struct.pack(f"<{len(cells)}I", *cells))
    xtape = [(B_STMQ, False, limb3(list(b_in["stRoot"])) + [tgo] + limb3(rso)),
             (B_STMA, True, limb3(list(h_out["stRoot"])) + [tgi] + limb3(rsi))]
    json.dump([[b, s, msg] for b, s, msg in xtape], open(f"{out}/xtape.json", "w"))
    for nm in ("pubs.bin", "expected_pubs.bin"):
        with open(f"{out}/{nm}", "wb") as f:
            f.write(struct.pack(f"<{len(pubs)}I", *[v % P for v in pubs]))
    json.dump(["SE", "RNG"], open(f"{out}/tables.json", "w"))
    json.dump([0, 450, 450], open(f"{out}/bnd.json", "w"))
    json.dump({"leaf": leaf, "cuts": [ca, cb], "pubs": pubs, "se_row0": dict(zip(SE_NAMES, row)),
               "d_in": d_in, "d_out": d_out}, open(f"{out}/t1-se.json", "w"))
    if "--template" in opt:
        json.dump(json.load(open(opt["--template"])), open(f"{out}/template.json", "w"), indent=1)
    print(f"SE dump [{leaf}] c{ca} -> c{cb}: d_in {d_in[:16]} d_out {d_out[:16]} (lane I chain), "
          f"STMQ tag_out {tgo}, STMA tag_in {tgi}, {len(pubs)} public values")


if __name__ == "__main__":
    main()
