#!/usr/bin/env python3
"""F-2: the `rt` enter leaf's dump (`ENT`, `M5T1/Ent.lean`).

  entgen.py PLAN.json OUT_DIR [--template T.json] [--mutant NAME]

The public values are the boundary pair of lane I's `RT enter` cut (`rtbnd.pair`: `BndRec.encode`
of `B_in` (408 B, out of a call) and `B_out` (784 B, in a call), digests = the plan's), one byte
per public value; the trace is one zero column of 4 rows. Mutants (each must be rejected):
`phase` (B_out phase 1 instead of 6), `gas` (B_out gasUsed + 1), `stroot` (B_out stRoot byte flipped),
`clock` (B_out t = 1)."""
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
    for k in ("--template", "--mutant"):
        if k in a:
            i = a.index(k)
            opt[k] = a[i + 1]
            a = a[:i] + a[i + 2:]
    plan, out = a
    os.makedirs(out, exist_ok=True)
    b_in, b_out, e_in, e_out, d_in, d_out = rtbnd.pair(plan, "RT enter")
    assert len(e_in) == 408 and len(e_out) == 784, "enter: eng record -> call record"
    pubs = list(e_in) + list(e_out)
    expected = list(pubs)
    m = opt.get("--mutant")
    if m:
        r = dict(b_out)
        if m == "phase":
            r["phase"] = 1
        elif m == "gas":
            r["gasUsed"] += 1
        elif m == "stroot":
            r["stRoot"] = bytes([r["stRoot"][0] ^ 1]) + r["stRoot"][1:]
        elif m == "clock":
            r["t"] = 1
        else:
            raise SystemExit(f"unknown mutant {m}")
        pubs = list(e_in) + list(rtbnd.bndrec.encode(r))
        print(f"mutant applied: [{m}]")
        # the statement is the claimed (mutated) boundary: the proof must fail on the constraints
        expected = list(pubs)
    with open(f"{out}/ENT.bin", "wb") as f:
        f.write(struct.pack("<II", 2, 1))
        f.write(b"\0" * 16)
    for nm, vs in (("pubs.bin", pubs), ("expected_pubs.bin", expected)):
        with open(f"{out}/{nm}", "wb") as f:
            f.write(struct.pack(f"<{len(vs)}I", *[v % P for v in vs]))
    json.dump(["ENT"], open(f"{out}/tables.json", "w"))
    json.dump([0, 408, 784], open(f"{out}/bnd.json", "w"))
    if "--template" in opt:
        json.dump(json.load(open(opt["--template"])), open(f"{out}/template.json", "w"), indent=1)
    print(f"ENT dump: d_in {d_in[:16]}.. d_out {d_out[:16]}.. (lane I plan), {len(pubs)} public values")


if __name__ == "__main__":
    main()
