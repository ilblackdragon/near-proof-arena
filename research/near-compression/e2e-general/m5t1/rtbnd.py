#!/usr/bin/env python3
"""F-2: the `rt` leaves' public boundary pair, from lane I's driver plan (`t1.py run` → plan.json).

`pair(plan, template)` returns the in / out records of the plan's `RT enter` or `RT resume` cut as
`BndRec.encode` bytes (lane I's `bndrec.py`, cross-checked there against Lean's `BndRec.encode`),
after checking that their digests are the plan's `d_in` / `d_out` (so a proof whose public values are
these bytes exposes exactly the driver's boundary digests). The `rt` AIRs' public values are these
bytes, one per public value (`BndLay.lean`: `engF` 408 B, `callF` 784 B)."""
import json
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "t1"))
import bndrec  # noqa: E402

HEXF = {n for n, k in bndrec.BND_FIELDS if k == "dig"}
WHEXF = {n for n, k in bndrec.WASM_FIELDS if k == "dig"}


def from_json(j):
    r = dict(j)
    for n in HEXF:
        r[n] = bytes.fromhex(r[n])
    r["outRcptAcc"] = [bytes.fromhex(d) for d in r["outRcptAcc"]]
    if r["wasm"] is not None:
        w = dict(r["wasm"])
        for n in WHEXF:
            w[n] = bytes.fromhex(w[n])
        r["wasm"] = w
    return r


def pair(plan_path, template):
    p = json.load(open(plan_path))
    segs = p["segments"]
    i = [s["template"] for s in segs].index(template)
    b_in = from_json(p["B_0"] if i == 0 else segs[i - 1]["B_out"])
    b_out = from_json(segs[i]["B_out"])
    e_in, e_out = bndrec.encode(b_in), bndrec.encode(b_out)
    assert bndrec.bdigest(e_in).hex() == segs[i]["d_in"], "plan d_in"
    assert bndrec.bdigest(e_out).hex() == segs[i]["d_out"], "plan d_out"
    return b_in, b_out, e_in, e_out, segs[i]["d_in"], segs[i]["d_out"]


if __name__ == "__main__":
    for t in ["RT enter", "RT resume"]:
        _, _, a, b, di, do = pair(sys.argv[1], t)
        print(t, len(a), len(b), di[:16], do[:16])
