#!/usr/bin/env python3
"""F-5: refresh the T1 data of `lean/M5T1/T1Enter.lean` from the enter leaf's dump.

    t1enter_lean.py ENTER_DUMP_DIR lean/M5T1/T1Enter.lean

ENTER_DUMP_DIR is `entgen.py`'s output (`pubs.bin`: the 1,284 public values = `BndRec.encode` of
`B_in` (450 B) and `B_out` (834 B), lane I's chain c2 -> c3 since F-5). Rewrites, in place, the
literal lists `t1EntBytesN`, `t1EntPub`, the record fields `t1_claimDigestN`, `t1_stRootN`,
`t1_ctxRootN`, `t1_outcomeAccN`, `t1_proposalsAccN`, `t1_bwAccN`, `t1_vmAccN`, `t1_outRcpt0N`,
`t1_vmCtxN` and the clear fields `t1Clear`; the theorems are unchanged (kernel-checked again by
`lake build`)."""
import os
import re
import struct
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "t1"))
import bndrec  # noqa: E402


def nat_block(xs, per=24, ind="   "):
    rows = [", ".join(str(x) for x in xs[i:i + per]) for i in range(0, len(xs), per)]
    return "[" + (",\n" + ind).join(rows) + "]"


def main():
    d, path = sys.argv[1], sys.argv[2]
    raw = open(f"{d}/pubs.bin", "rb").read()
    pubs = list(struct.unpack(f"<{len(raw) // 4}I", raw))
    assert len(pubs) == 1284 and all(x < 256 for x in pubs)
    b_in = bndrec.decode(bytes(pubs[:450]))
    b_out = bndrec.decode(bytes(pubs[450:]))
    assert bndrec.encode(b_in) == bytes(pubs[:450]) and bndrec.encode(b_out) == bytes(pubs[450:])
    s = open(path).read()

    def put(name, xs):
        nonlocal s
        pat = re.compile(r"(def %s : List Nat :=\n  )\[[^\]]*\]" % re.escape(name))
        assert pat.search(s), name
        s = pat.sub(lambda m: m.group(1) + nat_block(xs), s, count=1)

    put("t1EntBytesN", pubs)
    fields = {"t1_claimDigestN": b_in["claimDigest"], "t1_stRootN": b_in["stRoot"], "t1_ctxRootN": b_in["ctxRoot"],
              "t1_outcomeAccN": b_in["outcomeAcc"], "t1_proposalsAccN": b_in["proposalsAcc"], "t1_bwAccN": b_in["bwAcc"],
              "t1_vmAccN": b_in["vmAcc"], "t1_outRcpt0N": b_in["outRcptAcc"][0], "t1_vmCtxN": b_out["wasm"]["vmCtxDigest"]}
    for n, v in fields.items():
        put(n, list(v))
    pat = re.compile(r"(def t1EntPub : List Fp :=\n  )\[[^\]]*\]")
    assert pat.search(s)
    s = pat.sub(lambda m: m.group(1) + "[" + ", ".join(f"Fp.ofNat {x}" for x in pubs) + "]", s, count=1)
    r = b_in
    assert r["blockIdx"] == r["actionIdx"] == r["t"] == r["rPrepaid"] == r["rBurnt"] == r["rUsed"] == 0
    clear = (f"def t1Clear : ClearF := ⟨t1_claimDigest, 0, {r['receiptIdx']}, 0, 0, {r['gasUsed']}, "
             f"{r['gasBurnt']}, {r['balanceBurnt']}, {r['compute']}, 0, 0, 0⟩")
    s, n = re.subn(r"def t1Clear : ClearF := ⟨[^⟩]*⟩", clear, s, count=1)
    assert n == 1
    assert b_out["rPrepaid"] == 54000000000000
    open(path, "w").write(s)
    print(f"T1Enter data: d_in {bndrec.bdigest(bytes(pubs[:450])).hex()[:16]} d_out "
          f"{bndrec.bdigest(bytes(pubs[450:])).hex()[:16]}")


if __name__ == "__main__":
    main()
