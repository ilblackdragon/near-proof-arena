#!/usr/bin/env python3
"""F-2/F-3: the `rt` enter leaf's dump (`ENT`, `M5T1/Ent.lean`).

  entgen.py PLAN.json OUT_DIR --run LEAN_RUN.json [--template T.json] [--mutant NAME]

The public values are the boundary pair of lane I's `RT enter` cut in the M11i record shape
(`rtbnd.pair`: `BndRec.encode` of `B_in` (450 B, out of a call) and `B_out` (834 B, in a call: lane
A's `.pre` record with S2 `codeRoot = code hash ‖ 0^10`, the code hash = the receiver account's in
the Lean run)), one byte per public value; the trace is one zero column of 4 rows. Mutants (each
must be rejected): F-2's `phase` (B_out phase 1 instead of 6), `gas` (B_out gasUsed + 1), `stroot`
(B_out stRoot byte flipped), `clock` (B_out t = 1); F-3's `coderoot` (a pad byte of `codeRoot`
nonzero), `prefuel` (`.pre` fuel 1), `gasleft` (`.pre` gasLeft 1), `framesdig` (`.pre`
framesDigest byte flipped), `outrcpt` (the outgoing accumulator not carried), `inphase` (B_in
phase 2); F-6's `nonbyte` (claimDigest byte 0 of both records + 256: the copy holds, the value is
not a byte).
F-6: the AIR is `Ent.entAirB` = `ENT` + `RNG`: every public value is received on `RNG` (in-circuit
byte range; lane D's F-M9-1), `RNG.bin` counts them."""
import json
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rtbnd  # noqa: E402

P = 0x78000001


def main():
    a = sys.argv[1:]
    opt = {}
    for k in ("--template", "--mutant", "--run"):
        if k in a:
            i = a.index(k)
            opt[k] = a[i + 1]
            a = a[:i] + a[i + 2:]
    plan, out = a
    os.makedirs(out, exist_ok=True)
    ch = rtbnd.code_hash_of(opt["--run"])
    b_in, b_out, e_in, e_out, d_in, d_out = rtbnd.pair(plan, "RT enter", ch)
    assert len(e_in) == 450 and len(e_out) == 834, "enter: eng record -> call record"
    pubs = list(e_in) + list(e_out)
    expected = list(pubs)
    m = opt.get("--mutant")
    if m:
        r = dict(b_out)
        r["wasm"] = dict(r["wasm"])
        ri = dict(b_in)
        if m == "phase":
            r["phase"] = 1
        elif m == "gas":
            r["gasUsed"] += 1
        elif m == "stroot":
            r["stRoot"] = bytes([r["stRoot"][0] ^ 1]) + r["stRoot"][1:]
        elif m == "clock":
            r["t"] = 1
        elif m == "coderoot":
            r["wasm"]["codeRoot"] = r["wasm"]["codeRoot"][:41] + b"\x01"
        elif m == "prefuel":
            r["wasm"]["fuel"] = 1
        elif m == "gasleft":
            r["wasm"]["gasLeft"] = 1
        elif m == "framesdig":
            fd = r["wasm"]["framesDigest"]
            r["wasm"]["framesDigest"] = bytes([fd[0] ^ 1]) + fd[1:]
        elif m == "outrcpt":
            o = r["outRcptAcc"][0]
            r["outRcptAcc"] = [bytes([o[0] ^ 1]) + o[1:]]
        elif m == "inphase":
            ri["phase"] = 2
        elif m == "nonbyte":
            pass
        else:
            raise SystemExit(f"unknown mutant {m}")
        pubs = list(rtbnd.bndrec.encode(ri)) + list(rtbnd.bndrec.encode(r))
        if m == "nonbyte":
            # F-6: claimDigest byte 0 of both records + 256 (a copied field: the copy holds; F-5's
            # AIR accepted it, `pubBytes` must not)
            pubs[0] += 256
            pubs[450] += 256
        print(f"mutant applied: [{m}]")
        # the statement is the claimed (mutated) boundary: the proof must fail on the constraints
        expected = list(pubs)
    with open(f"{out}/ENT.bin", "wb") as f:
        f.write(struct.pack("<II", 2, 1))
        f.write(b"\0" * 16)
    # F-6: `ENT` receives every public value on `RNG` (`Ids.pubBytes`); RNG row v counts them
    rng = [0] * 256
    for v in pubs:
        if v < 256:
            rng[v] += 1
    with open(f"{out}/RNG.bin", "wb") as f:
        f.write(struct.pack("<II", 8, 21))
        cells = []
        for v in range(256):
            cells += [v] + [(rng[v] >> t) & 1 for t in range(20)]
        f.write(struct.pack(f"<{len(cells)}I", *cells))
    for nm, vs in (("pubs.bin", pubs), ("expected_pubs.bin", expected)):
        with open(f"{out}/{nm}", "wb") as f:
            f.write(struct.pack(f"<{len(vs)}I", *[v % P for v in vs]))
    json.dump(["ENT", "RNG"], open(f"{out}/tables.json", "w"))
    json.dump([0, 450, 834], open(f"{out}/bnd.json", "w"))
    if "--template" in opt:
        json.dump(json.load(open(opt["--template"])), open(f"{out}/template.json", "w"), indent=1)
    print(f"ENT dump: d_in {d_in} d_out {d_out} (lane I chain / plan pair), code hash {ch.hex()}, {len(pubs)} public values")


if __name__ == "__main__":
    main()
