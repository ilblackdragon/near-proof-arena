#!/usr/bin/env python3
"""F-5 / F-7: the STATE engine half's leaf dump (`SE` + `SH`, `M5T1/Se.lean`, `M5T1/Sh.lean`) for one
STATE leaf of lane I's chain.

  segen.py CHAIN.json LEAF OUT_DIR --f7 F7EVAL.json --names SE_NAMES.json [--inputs T1_INPUTS.json]
           [--template T.json] [--mutant NAME] [--cx]

LEAF is a leaf name of the chain's leaf table (`STATE seg A` = c1 → c2, `STATE seg B` = c7 → c8,
`finalize` = c8 → c9). The public values are the two cut records, `BndRec.encode` bytes (`engF`,
450 B each), taken from the chain unchanged. F-7: `SE` row 0 opens the input `stRoot` (lane B's
`StCommit.ser`: tag, working-set root, `wsLen`, trie, `idx`, `rest`; the M14 values of lane E's
`m14` field) and lane E's `encRestI` remainder in / out; the preimages are lane F's Lean evaluation
(`lean/join-check/f7-eval.sh`: `Ser.enc (restMove (restOfB v))`, `d_keys`, `d_shape`, …), and every
hash is an `SH` run through the native SHA-512 chip (`comps.json`). `XTAPE` is the T1 stand-in for
lane B's `STC`: it receives `STMQ [r_in, tag_out, rest_out]` and answers `STMA [r_out, tag_in,
rest_in]` with `r_out` = **`STC`'s close computed from the `STMQ` it receives** (`StCommit.ser` of
`tag_out`, the output cut's working-set root / `wsLen` / trie / `idx`, and `rest_out`), so a leaf
that closes a different remainder gets a different `r_out` and fails against its public `B_out`.

Mutants (each must be rejected by the leaf). F-5 / F-6: `phase`, `vmacc`, `prepaid`, `gasburnt`,
`ctxcopy`, `claimcopy`, `clock`, `incall`, `stroot`, `nonbyte`. **F-7** (the stand-in follows the
mutated metas, so only the leaf's own rows and the simulated `STC` close can reject):
`tagin` (wrong tag: the opened tag ≠ the input `stRoot`'s), `wsopen` (the opened working-set root
flipped), `restin` (the received `rest_in` flipped), `queue` (wrong queue: the opened `d_queue`
flipped — its pop / copy starts from a queue the input does not commit to), `movein` (the opened
moving state's preimage byte flipped), `moveout` (wrong moving-state update: the stepped moving
part's byte flipped, `d_move'` / `rest_out` recomputed), `tagout` (wrong output tag), `static`
(`d_static'` ≠ the opened `d_static`, `rest_out` recomputed), `finqueue` (finalize: `d_queue'` ≠
`d_queue`), `finkeys` (finalize: `d_keys` flipped in both static hashes).
"""
import hashlib
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rtbnd  # noqa: E402
from tracegen import IV384, Trace, bits, compress512, pad512, split4, split_rng, wlimbs  # noqa: E402

bndrec = rtbnd.bndrec
P = 0x78000001
B_RNG, B_STMQ, B_STMA = 2, 17, 18
COPY = ["claimDigest", "blockIdx", "actionIdx", "t", "ctxRoot", "bwAcc"]
STATE_LEAVES = ("STATE seg A", "STATE seg B", "finalize")
DEFAULT_INPUTS = os.path.join(HERE, "..", "t1", "data", "t1-inputs.json")


def bdigest(b):
    return hashlib.sha384(bytes(b)).digest()[:42]


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


def ser(tag, ws, wslen, trie, idx, rest):
    """lane B's `StCommit.ser` (139 B)."""
    assert len(ws) == 48 and len(trie) == 32 and len(rest) == 42 and tag < 256
    return bytes([tag]) + ws + wslen.to_bytes(8, "little") + trie + idx.to_bytes(8, "little") + rest


def opening(m14, f7, cut):
    """The `stRoot` opening of a cut (M14 values) and lane F's preimages."""
    m, e = m14["cuts"][f"c{cut}"], f7["cuts"][f"c{cut}"]
    for k in ("rest", "d_queue", "d_move"):
        assert m.get(k, e[k]) == e[k], f"c{cut}: {k} (lane E m14 vs lane F f7-eval)"
    o = dict(tag=int(m["tag"]), ws=bytes.fromhex(m["ws_root"]), wsLen=int(m["wsLen"]), trie=bytes.fromhex(m["trie"]),
             idx=int(m["idx"]), rest=bytes.fromhex(m["rest"]), dS=bytes.fromhex(e["d_static"]),
             dQ=bytes.fromhex(e["d_queue"]), dM=bytes.fromhex(e["d_move"]), dK=bytes.fromhex(e["d_keys"]),
             dSh=bytes.fromhex(e["d_shape"]), move=bytes.fromhex(e["move"]))
    assert bdigest(o["move"]) == o["dM"] and bdigest(o["dS"] + o["dQ"] + o["dM"]) == o["rest"]
    assert bdigest(o["dK"] + o["dSh"]) == o["dS"]
    assert bdigest(ser(o["tag"], o["ws"], o["wsLen"], o["trie"], o["idx"], o["rest"])) == bytes.fromhex(m["stRoot"])
    return o


class Sh:
    """`SH` rows and the chip's compressions (`Sh.lean`)."""

    def __init__(self, names):
        self.t = Trace(names)
        self.comps = []
        self.rng = []

    def run(self, hid, msg, fx):
        """One hash of `msg` (unpadded): rows, compressions, RNG values; returns (digest42, nblocks)."""
        m = pad512(msg)
        nb = len(m) // 128
        h = list(IV384)
        for k in range(nb):
            blk = m[128 * k:128 * (k + 1)]
            ws = [int.from_bytes(blk[8 * i:8 * i + 8], "big") for i in range(16)]
            o = compress512(h, ws)
            r = self.t.row()
            for nm, v in (("act", 1), ("fst", int(k == 0)), ("lst", int(k == nb - 1)), ("hid", hid),
                          ("cid", 128 * len(self.comps)), ("fx", int(fx)), ("bi", k)):
                self.t.set(r, nm, v)
            self.t.setv(r, "blk", list(blk))
            sp = []
            for i in range(16):
                sp += split4(blk[8 * i:8 * i + 8])
            self.t.setv(r, "bsp", sp)
            self.t.setv(r, "h", [l for x in h for l in wlimbs(x)])
            self.t.setv(r, "o", [l for x in o for l in wlimbs(x)])
            self.rng += list(blk) + [v for i in range(16) for v in split_rng(sp[4 * i:4 * i + 4])]
            self.comps.append(dict(h=[str(x) for x in h], block=[str(x) for x in ws]))
            if k == nb - 1:
                dgb = b"".join(x.to_bytes(8, "big") for x in o[:6])
                assert dgb == hashlib.sha384(msg).digest(), "SH: SHA-384 chain"
                dsp = []
                for t in range(6):
                    dsp += split4(dgb[8 * t:8 * t + 8])
                self.t.setv(r, "dg", list(dgb))
                self.t.setv(r, "dsp", dsp)
                self.rng += list(dgb) + [v for t in range(6) for v in split_rng(dsp[4 * t:4 * t + 4])]
            h = o
        return dgb[:42], nb


def main():
    a = sys.argv[1:]
    opt = {}
    for k in ("--template", "--mutant", "--f7", "--inputs", "--names"):
        if k in a:
            i = a.index(k)
            opt[k] = a[i + 1]
            a = a[:i] + a[i + 2:]
    cx = "--cx" in a
    a = [x for x in a if x != "--cx"]
    chain_path, leaf, out = a
    ch = json.load(open(chain_path))
    f7 = json.load(open(opt["--f7"]))
    m14 = json.load(open(opt.get("--inputs", DEFAULT_INPUTS)))["m14"]
    ca, cb, b_in, b_out = pair(ch, leaf)
    check_rules(b_in, b_out)
    d_in, d_out = bndrec.digest(b_in).hex(), bndrec.digest(b_out).hex()
    assert (d_in, d_out) == (ch["digests"][ca], ch["digests"][cb]), "digests = the chain's"
    oi, oo = opening(m14, f7, ca), opening(m14, f7, cb)
    assert bdigest(ser(oi["tag"], oi["ws"], oi["wsLen"], oi["trie"], oi["idx"], oi["rest"])) == b_in["stRoot"], "opening = B_in.stRoot"
    assert bdigest(ser(oo["tag"], oo["ws"], oo["wsLen"], oo["trie"], oo["idx"], oo["rest"])) == b_out["stRoot"], "close = B_out.stRoot"
    fin = int(leaf == "finalize")
    none_enc = bytes.fromhex(f7["none_enc"])
    dShN = bdigest(none_enc)
    if fin:
        assert (oi["tag"], oo["tag"]) == (8, 3) and oo["dQ"] == oi["dQ"] and oo["dK"] == oi["dK"] and oo["dSh"] == dShN
    else:
        assert oo["dS"] == oi["dS"], "static part copied"
    # the leaf's values (honest), then the mutation
    v = dict(tgi=oi["tag"], wsi=oi["ws"], wli=oi["wsLen"].to_bytes(8, "little"), tri=oi["trie"],
             ixi=oi["idx"].to_bytes(8, "little"), rsi=oi["rest"], dS=oi["dS"], dQ=oi["dQ"], dM=oi["dM"],
             dK=oi["dK"] if fin else bytes(42), dSh=oi["dSh"] if fin else bytes(42), dShN=dShN if fin else bytes(42),
             x=oi["move"], xo=oo["move"], tgo=oo["tag"], dSo=oo["dS"], dQo=oo["dQ"])
    m = opt.get("--mutant")
    flip = lambda b, i=0: b[:i] + bytes([b[i] ^ 1]) + b[i + 1:]  # noqa: E731
    pubs_in, pubs_out = dict(b_in), dict(b_out)
    if m:
        if m == "phase":
            pubs_out["phase"] = 6
        elif m == "vmacc":
            pubs_out["vmAcc"] = bndrec.bdigest(b"vm")
        elif m == "prepaid":
            pubs_out["rPrepaid"] = 1
        elif m == "gasburnt":
            pubs_out["gasBurnt"] = pubs_out["gasUsed"] + 1
        elif m == "ctxcopy":
            pubs_out["ctxRoot"] = flip(pubs_out["ctxRoot"])
        elif m == "claimcopy":
            pubs_out["claimDigest"] = flip(pubs_out["claimDigest"])
        elif m == "clock":
            pubs_out["t"] = 1
        elif m == "incall":
            pass
        elif m == "stroot":
            pubs_out["stRoot"] = flip(pubs_out["stRoot"])
        elif m == "nonbyte":
            pass
        elif m == "tagin":
            v["tgi"] = v["tgi"] + 1
        elif m == "wsopen":
            v["wsi"] = flip(v["wsi"], 5)
        elif m == "restin":
            v["rsi"] = flip(v["rsi"], 7)
        elif m == "queue":
            v["dQ"] = flip(v["dQ"], 3)
            if fin:
                v["dQo"] = v["dQ"]
        elif m == "movein":
            v["x"] = flip(v["x"], len(v["x"]) // 2)
        elif m == "moveout":
            v["xo"] = flip(v["xo"], len(v["xo"]) // 2)
        elif m == "tagout":
            v["tgo"] = v["tgo"] + 1
        elif m == "static":
            if fin:
                raise SystemExit(3)
            v["dSo"] = flip(v["dSo"], 11)
        elif m == "finqueue":
            if not fin:
                raise SystemExit(3)
            v["dQo"] = flip(v["dQo"], 2)
        elif m == "finkeys":
            if not fin:
                raise SystemExit(3)
            v["dK"] = flip(v["dK"], 9)
        else:
            raise SystemExit(f"unknown mutant {m}")
        print(f"mutant applied: [{m}]")
    # the hashes (SH runs); a mutated preimage hashes to its own digest, the SE row keeps the claimed one
    se_names_all = json.load(open(opt["--names"]))
    sh = Sh(se_names_all["SH"])
    dM = v["dM"]                                   # the opened d_move (claimed)
    dMo_x, nbo = sh.run(7, v["xo"], False)         # d_move' := the stepped preimage's digest
    _, nbi = sh.run(6, v["x"], False)              # movein: SH hashes the flipped preimage; SE claims dM
    dMo = dMo_x
    if fin:
        dSo = bdigest(v["dK"] + v["dShN"])
        if m == "finkeys":
            pass                                   # dS (opened) stays the input's: hid 3 fails
    else:
        dSo = v["dSo"]
    rso = bdigest(dSo + v["dQo"] + dMo)
    ser_in = ser(v["tgi"] if v["tgi"] < 256 else 0, v["wsi"], int.from_bytes(v["wli"], "little"), v["tri"],
                 int.from_bytes(v["ixi"], "little"), v["rsi"])
    sh.run(0, ser_in, True)
    sh.run(1, v["dS"] + v["dQ"] + dM, True)
    sh.run(2, dSo + v["dQo"] + dMo, True)
    if fin:
        sh.run(3, v["dK"] + v["dSh"], True)
        sh.run(4, v["dK"] + v["dShN"], True)
        sh.run(5, none_enc, True)
    nbc = 0
    if cx:
        ienc = b"\x01" + bytes.fromhex(f7["intake_enc"])
        assert bdigest(ienc) == b_in["ctxRoot"], "ctxD (.intake I) = B_in.ctxRoot"
        _, nbc = sh.run(8, ienc, False)
    # the public records
    e_in = bndrec.encode(pubs_in)
    if m == "incall":
        e_in = bytearray(e_in)
        e_in[42 + 8 * 4] = 1
        e_in = bytes(e_in)
    e_out = bndrec.encode(pubs_out)
    assert len(e_in) == 450 and len(e_out) == 450
    pubs = list(e_in) + list(e_out)
    if m == "nonbyte":
        pubs[0] += 256
        pubs[450] += 256
    # SE row 0
    se = Trace(se_names_all["SE"])
    r = se.row()
    se.row()
    se.set(r, "tgo", v["tgo"]); se.setv(r, "rso", list(rso)); se.set(r, "tgi", v["tgi"]); se.setv(r, "rsi", list(v["rsi"]))
    se.set(r, "fin", fin); se.set(r, "cx", int(cx))
    for nm in ("wsi", "wli", "tri", "ixi", "dS", "dQ", "dSo", "dQo", "dK", "dSh", "dShN"):
        se.setv(r, nm, list(v[nm] if nm not in ("dSo",) else dSo))
    se.setv(r, "dM", list(dM)); se.setv(r, "dMo", list(dMo))
    se.set(r, "nbi", nbi - 1); se.set(r, "nbo", nbo - 1); se.set(r, "nbc", max(nbc - 1, 0))
    # RNG
    rng = [0] * 256
    vals = list(rso) + list(v["rsi"]) + [v["tgi"] + 1, v["tgi"], v["tgo"]]
    for nm, w in (("wsi", 48), ("wli", 8), ("tri", 32), ("ixi", 8), ("dS", 42), ("dQ", 42), ("dM", 42),
                  ("dSo", 42), ("dQo", 42), ("dMo", 42), ("dK", 42), ("dSh", 42), ("dShN", 42)):
        vals += [se.get(r, nm, j) for j in range(w)]       # `Se.byteGroups`
    vals += sh.rng
    vals += pubs
    for x in vals:
        if x < 256:
            rng[x] += 1
    os.makedirs(out, exist_ok=True)
    se.write(f"{out}/SE.bin", min_log=1)
    sh.t.write(f"{out}/SH.bin")
    rt = Trace(se_names_all["RNG"])
    for x in range(256):
        row = rt.row()
        rt.set(row, "v", x)
        rt.setv(row, "m", bits(rng[x], 20))
    rt.write(f"{out}/RNG.bin")
    json.dump(sh.comps, open(f"{out}/comps.json", "w"))
    # XTAPE: lane B's STC stand-in, closing what it receives (module doc)
    tgo_c = v["tgo"] % 256
    r_out = bdigest(ser(tgo_c, oo["ws"], oo["wsLen"], oo["trie"], oo["idx"], rso))
    if m == "stroot":
        r_out = b_out["stRoot"]                    # the honest STC answer; the public B_out is flipped
    xtape = [(B_STMQ, False, limb3(list(b_in["stRoot"])) + [v["tgo"]] + limb3(rso)),
             (B_STMA, True, limb3(list(r_out)) + [v["tgi"]] + limb3(v["rsi"]))]
    json.dump([[b, s, msg] for b, s, msg in xtape], open(f"{out}/xtape.json", "w"))
    for nm in ("pubs.bin", "expected_pubs.bin"):
        with open(f"{out}/{nm}", "wb") as f:
            f.write(struct.pack(f"<{len(pubs)}I", *[x % P for x in pubs]))
    json.dump(["SE", "RNG", "SH"], open(f"{out}/tables.json", "w"))
    json.dump([0, 450, 450], open(f"{out}/bnd.json", "w"))
    json.dump({"leaf": leaf, "cuts": [ca, cb], "pubs": pubs, "se_row0": dict(zip(se.names, se.rows[0])),
               "d_in": d_in, "d_out": d_out, "sh_rows": len(sh.t.rows), "compressions": len(sh.comps),
               "move_in": len(v["x"]), "move_out": len(v["xo"]), "cx": cx, "intake_blocks": nbc},
              open(f"{out}/t1-se.json", "w"))
    if "--template" in opt:
        json.dump(json.load(open(opt["--template"])), open(f"{out}/template.json", "w"), indent=1)
    print(f"SE dump [{leaf}] c{ca} -> c{cb}: d_in {d_in[:16]} d_out {d_out[:16]} (lane I chain), "
          f"tags {v['tgi']} -> {v['tgo']}, fin {fin}, SH {len(sh.t.rows)} rows / {len(sh.comps)} compressions "
          f"(d_move preimages {len(v['x'])} -> {len(v['xo'])} B{', intake ' + str(nbc) + ' blocks' if cx else ''}), "
          f"{len(pubs)} public values")


if __name__ == "__main__":
    main()
