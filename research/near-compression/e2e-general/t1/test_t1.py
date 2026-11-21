"""Lane I (I-2) driver tests: canonical S, BndRec codec, Lean cross-checks, loud boundary mismatches.

    python3 -m pytest -q research/near-compression/e2e-general/t1/test_t1.py

The Lean cross-checks run `lake env lean --run` in the main checkout's v3 package (built oleans,
no build) and are skipped when that package or T1's corpus case is absent.
"""
import copy
import os
import shutil
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bndrec  # noqa: E402
import stmt  # noqa: E402
import t1  # noqa: E402

T1_CASE = "/data/illia/nearproof-deps/corpora/d3c8/d3/02-h10196-s3"
HAVE_T1 = os.path.exists(os.path.join(T1_CASE, "claim.bin"))
HAVE_LEAN = shutil.which("lake") is not None and os.path.isdir(
    os.path.join(stmt.LEAN_PKG, ".lake/build/lib/lean/NearSpecV3/E2E"))


def t1_claim():
    return open(os.path.join(T1_CASE, "claim.bin"), "rb").read()


def test_bndrec_selftest():
    assert bndrec.selftest()


@pytest.mark.skipif(not HAVE_T1, reason="T1 corpus case absent")
def test_t1_statement_canonical():
    claim = t1_claim()
    pc = stmt.parse_claim(claim)
    s = stmt.statement_bytes(claim, pc)
    b0, b1 = pc["secB"]
    assert len(s) == stmt.T1_S_LEN
    assert stmt.claim_digest(s).hex() == stmt.T1_CLAIM_DIGEST
    assert s[b0:b0 + 4] == b"\x00\x00\x00\x00"
    # assemble_splice: S with the block vector spliced back is the claim
    assert stmt.splice_secB(s, claim[b0:b1], b0) == claim


@pytest.mark.skipif(not (HAVE_T1 and HAVE_LEAN), reason="T1 case or Lean v3 package absent")
def test_t1_statement_lean(tmp_path):
    p = str(tmp_path / "claim.bin")
    open(p, "wb").write(t1_claim())
    rows = stmt.lean_stmt([p])
    r = stmt.lean_stmt_compare(t1_claim(), rows[p])
    assert r["ok"], r
    assert r["S_len"] == 1007 and r["claimDigest"] == stmt.T1_CLAIM_DIGEST


@pytest.mark.skipif(not HAVE_LEAN, reason="Lean v3 package absent")
def test_bndrec_lean(tmp_path):
    a = bndrec.blank(bndrec.bdigest(b"abc"))
    b = copy.deepcopy(a)
    b.update(phase=6, inCall=True, wasm=bndrec.wasm_blank(), gasUsed=2 ** 64 - 1, balanceBurnt=2 ** 100,
             outRcptAcc=[bndrec.bdigest(b"x"), bndrec.bdigest(b"y")])
    b["wasm"].update(pc=77, memRoot=bndrec.bdigest(b"m"))
    res = bndrec.lean_check([a, b], str(tmp_path))
    assert res["ok"] is True, res
    # a record the Lean side would encode differently is caught
    bad = copy.deepcopy(b)
    bad["gasUsed"] = 2 ** 64  # out of u64 range: Python refuses to encode it
    with pytest.raises(AssertionError):
        bndrec.encode(bad)


def _bnd(t_in, t_out, halted, mem_in, mem_out, g_out, g0=100):
    side = lambda t, mem, g: {"pc": 0, "t": t, "S": 0, "sb": 0, "cid": 0, "S_seg": 0, "segb": g, "g": g,  # noqa: E731
                              "ctx": "00" * 48, "mem": mem, "nblk": 64, "depth": 6}
    return {"in": side(t_in, mem_in, g0), "out": side(t_out, mem_out, g_out), "halted": halted, "memsize": 65536}


def test_wasm_boundary_mismatch_is_loud():
    prep = {"mem": 65536, "data": [1, 2], "dataEnd": 2, "records": [[0, 66]], "hosts": [], "funcs": [[0]], "fn": 0,
            "g0": 100, "gFinal": 90, "steps": 4}
    r0 = t1.mem_root({0: 1, 1: 2}, 64)
    good = [_bnd(0, 2, 0, r0, r0, 95), _bnd(2, 4, 1, r0, r0, 90)]
    good[1]["in"] = dict(good[0]["out"])
    t1.MISMATCHES.clear()
    rows = t1.wasm_lean_checks({"index": 0}, prep, good, 2)
    assert all(x["equal"] is not False for x in rows) and not t1.MISMATCHES
    bad = copy.deepcopy(good)
    bad[1]["out"]["g"] = 91          # final gas disagrees with the Lean tape
    bad[0]["in"]["mem"] = "11" * 48  # initial memory root disagrees with the Lean image
    t1.wasm_lean_checks({"index": 0}, prep, bad, 2)
    assert len(t1.MISMATCHES) == 2
    t1.MISMATCHES.clear()
