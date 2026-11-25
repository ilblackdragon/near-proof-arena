"""Lane I (I-2) driver tests: canonical S, BndRec codec, Lean cross-checks, loud boundary mismatches.

    python3 -m pytest -q research/near-compression/e2e-general/t1/test_t1.py

The Lean cross-checks run `lake env lean --run` in the main checkout's v3 package (built oleans,
no build) and are skipped when that package or T1's corpus case is absent.
"""
import copy
import hashlib
import json
import os
import shutil
import sys

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import bndrec  # noqa: E402
import chain  # noqa: E402
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


# ---------------------------------------------------------------------------
# I-2 (2026-11-25): the leaf chain under the current boundary conventions (`chain.py`)
# ---------------------------------------------------------------------------
def t1_inputs():
    return json.load(open(chain.INPUTS))


def test_chain_fixture_conventions():
    inp = t1_inputs()
    c = chain.build(inp)
    assert len(c) == 11 and chain.check_conventions(c, inp) == []
    ds = chain.digests(c)
    assert chain.chain_ok(chain.leaf_pairs(c), ds[0], ds[-1])
    for r in c:
        assert bndrec.decode(bndrec.encode(r)) == r
    # record sizes: init / done (empty outRcptAcc) 408 B, engine 450 B, call 834 B (lane F's engF / callF)
    assert [len(bndrec.encode(r)) for r in c] == [408, 450, 450, 834, 834, 834, 834, 450, 450, 450, 408]
    # E2E-M14: every cut distinct (c7 ≠ c8: the position tag 7 → 8 and `rest`)
    assert len(set(ds)) == 11
    # the accumulators are the Lean run's chainD Ser.enc; FunctionCall receipt = one append each
    b, a = inp["acc"]["before"], inp["acc"]["after"]
    assert c[2]["outcomeAcc"].hex() == b["outcomesChain"] and c[7]["outRcptAcc"] == [bytes.fromhex(a["outgoingChain"])]
    assert bndrec.bdigest(c[6]["outcomeAcc"] + bytes.fromhex(a["outcomes"][-1])) == c[7]["outcomeAcc"]
    assert bndrec.bdigest(c[6]["outRcptAcc"][0] + bytes.fromhex(a["outgoing"][-1])) == c[7]["outRcptAcc"][0]
    # M12: resume outputs receiptIdx + 1 and clears the call fields; done carries the header outputs
    assert (c[6]["receiptIdx"], c[7]["receiptIdx"]) == (1, 2) and c[7]["rPrepaid"] == 0
    assert c[10]["gasUsed"] == inp["gasUsed"] == 1577739758301 and c[10]["compute"] == 0
    # M13: start commits R_0 (lane B's IF R_in) through stRoot (M14: tag 1, the Lean-evaluated encRestI rest)
    rest = {k: bytes.fromhex(v["rest"]) for k, v in inp["m14"]["cuts"].items()}
    assert c[1]["stRoot"] == chain.st_commit(1, bytes.fromhex(inp["R_0"]), 17, bytes.fromhex(inp["prev_state_root"]),
                                             0, rest["c1"])
    assert c[3]["wasm"]["codeRoot"].hex() == inp["call"]["code_sha256"] + "00" * 10
    # B-T4: init / done carry stD .none (the kernel-evaluated constant = its record recomputed); c2 … c6
    # carry R_A (STATE seg A's output root), c7, c8 R_n. M14: the position tags (incoming 7, yields _ _ 0 8,
    # done 3) and encRestI rests; at done (c9) no overlay: the empty tree's root, wsLen 0, trie 0^32
    assert c[0]["stRoot"] == c[10]["stRoot"] == chain.ST_NONE == chain.st_none()
    ra, rn = bytes.fromhex(inp["R_A"]), bytes.fromhex(inp["R_n"])
    tr = bytes.fromhex(inp["prev_state_root"])
    assert all(c[k]["stRoot"] == chain.st_commit(7, ra, 17, tr, 0, rest["c2"]) for k in range(2, 7))
    assert c[7]["stRoot"] == chain.st_commit(7, rn, 17, tr, 0, rest["c7"])
    assert c[8]["stRoot"] == chain.st_commit(8, rn, 17, tr, 0, rest["c8"])
    assert c[9]["stRoot"] == chain.st_commit(3, chain.ws_empty(), 0, bytes(32), 0, rest["c9"])
    # M14: ctxRoot = ctxD (.intake I) at every engine / call cut
    assert all(c[k]["ctxRoot"].hex() == inp["m14"]["ctx_intake"] for k in range(1, 10))
    assert c[4]["wasm"]["gasLeft"] == inp["call"]["g0"] and c[6]["wasm"]["gasLeft"] == 0


def test_chain_violations_are_loud():
    inp = t1_inputs()
    c = chain.build(inp)
    bad = copy.deepcopy(c)
    bad[7]["receiptIdx"] = bad[6]["receiptIdx"]          # F-3's copying resume
    bad[5]["t"] = 13                                     # run4's in-call clock
    bad[0]["claimDigest"] = bytes.fromhex(inp["claimDigest_S"])
    v = chain.check_conventions(bad, inp)
    assert any("receiptIdx + 1" in x for x in v) and any(x.startswith("c5: M12") for x in v)
    assert any(x.startswith("c0: M12") for x in v)
    pairs = chain.leaf_pairs(c)
    pairs[4] = (pairs[4][0], "00" * 42)                  # a leaf whose output does not open the next input
    assert not chain.chain_ok(pairs)
    # the saved F-3 enter leaf's digests (pre-M12 record) do not chain with the plan's neighbours
    pairs = chain.leaf_pairs(c)
    pairs[2] = ("b850f1e5389c5fba6ebbcd4d0abf7c81c54b49a7ef69bc55fee6fa7879d394f7a944be77eb29e574c39c",
                "c320b92b892d0f60463568e636a10e36d663e338addac886ec9a2863f4653c70778fe6ac08a90facfb50")
    assert not chain.chain_ok(pairs)
    # a leaf exposing a pre-M12 record is reported field by field
    old = dict(c[2], claimDigest=bytes.fromhex(inp["claimDigest_S"]), bwAcc=bndrec.ZERO)
    row = chain._rec_row("x", None, old, c[3], c[2], c[3], "", "")
    assert not row["in_equal"] and row["out_equal"] and row["diff_in"] == ["claimDigest", "bwAcc"]


def test_chain_m14_rest():
    """E2E-M14: the committed Lean evaluation of the engine cuts, recomputed / cross-checked in Python."""
    inp = t1_inputs()
    assert chain.rest_check(inp) == []
    m = inp["m14"]["cuts"]
    assert [(n, int(m[n]["tag"])) for n in chain.M14_CUTS] == [("c1", 1), ("c2", 7), ("c7", 7), ("c8", 8), ("c9", 3)]
    # d_static is copied along the run until done; done keeps d_keys and swaps d_shape for the constant
    assert len({m[n]["d_static"] for n in ("c1", "c2", "c7", "c8")}) == 1 != len({m[n]["d_static"] for n in chain.M14_CUTS})
    assert m["c9"]["d_keys"] == m["c1"]["d_keys"] and m["c9"]["d_shape"] == inp["m14"]["d_shape_none"]
    # receipt 1 is popped by the resume (c2's queue = [receipt 1], c7's = []); c7 → c8 moves the position only
    assert len(m["c2"]["queue"]) == 1 and m["c7"]["queue"] == [] and m["c7"]["d_queue"] == bndrec.bdigest(b"").hex()
    assert m["c7"]["d_move"] != m["c8"]["d_move"] and m["c7"]["d_static"] == m["c8"]["d_static"]
    # a mutated evaluation is reported
    bad = copy.deepcopy(inp)
    bad["m14"]["cuts"]["c8"]["tag"] = "7"
    bad["m14"]["cuts"]["c2"]["queue"] = []
    v = chain.rest_check(bad)
    assert any(x.startswith("c8: tag") for x in v) and any(x.startswith("c2: d_queue") for x in v)


M5A_PKG = os.path.join(HERE, "..", "m5a", "lean")
HAVE_M5A = shutil.which("lake") is not None and os.path.isdir(os.path.join(M5A_PKG, ".lake/build/lib/lean/StateM5a"))


@pytest.mark.skipif(not (HAVE_T1 and HAVE_M5A), reason="T1 case or lane B's built package absent")
def test_chain_m14_lean(tmp_path):
    """E2E-M14: re-run the Lean evaluator (`join/rest-eval.sh`, lane B's package next to this file) on T1:
    the committed `m14` values (tags, rests, the remainder's digests, ctxD (.intake I), stRoot) are Lean's."""
    inp = t1_inputs()
    got = chain.m14_eval(inp, T1_CASE, str(tmp_path), M5A_PKG)
    want = inp["m14"]
    assert got["ctx_intake"] == want["ctx_intake"] and got["d_shape_none"] == want["d_shape_none"]
    for n in chain.M14_CUTS:
        for k in ("pos", "tag", "fits", "wsLen", "trie", "d_keys", "d_shape", "d_static", "d_queue", "d_move", "rest",
                  "queue", "stRoot", "written"):
            assert got["cuts"][n][k] == want["cuts"][n][k], (n, k)
    c = chain.build(inp)
    for i, n in ((1, "c1"), (2, "c2"), (7, "c7"), (8, "c8"), (9, "c9")):
        assert c[i]["stRoot"].hex() == got["cuts"][n]["stRoot"], n


@pytest.mark.skipif(not HAVE_T1, reason="T1 corpus case absent")
def test_chain_ctx_raw():
    inp = t1_inputs()
    cb, wb = t1_claim(), open(os.path.join(T1_CASE, "witness.bin"), "rb").read()
    assert hashlib.sha256(cb).hexdigest() == inp["claim_sha256"]
    assert bndrec.bdigest(chain.raw_pre(cb, wb, inp["lB"])).hex() == inp["ctx_raw_be"]
    assert bndrec.bdigest(chain.raw_pre(cb, wb, inp["lB"], "little")).hex() == inp["ctx_raw_le"] != inp["ctx_raw_be"]


@pytest.mark.skipif(not (HAVE_T1 and HAVE_LEAN), reason="T1 case or Lean v3 package absent")
def test_chain_lean(tmp_path):
    inp = t1_inputs()
    c = chain.build(inp)
    res = bndrec.lean_check(c, str(tmp_path))
    assert res["ok"] is True and [r["digest"] for r in res["rows"]] == chain.digests(c)
    cs = chain.lean_consts(inp, t1_claim(), open(os.path.join(T1_CASE, "witness.bin"), "rb").read(), str(tmp_path))
    assert cs["ok"] is True, cs
    assert cs["rows"]["u32_lB"]["lean"] == "00001367"     # ViewE.u32 is big-endian


HAVE_LEAVES = all(os.path.exists(p) for p in list(chain.SAVED.values()) + list(chain.SAVED_B.values()))


@pytest.mark.skipif(not HAVE_LEAVES, reason="saved leaves absent")
def test_chain_saved_leaves():
    inp = t1_inputs()
    rows, _ = chain.leaf_table(chain.build(inp), inp)
    r = {x["leaf"].split(" (")[0]: x for x in rows}
    # G-5: INIT hashes big-endian u32 (I2b-1) and FINAL ViewE's done encodings; both match the chain
    assert all(r["INIT"]["checks"].values()) and r["INIT"]["in_equal"]
    assert all(r["FINAL"]["checks"].values()) and r["FINAL"]["out_equal"]
    assert all(r["PREP"]["checks"].values())
    # B-T4: lane B's leaves cut at the rt boundaries; every STC r_in / r_out is the chain's stRoot and the
    # records assembled with them are the chain's cuts, digest for digest
    # E2E-M14 moved c1 … c9's stRoot (tag, rest) and ctxRoot: a leaf saved before M14 differs exactly there
    # (m14_stale) until its lane re-proves it on this chain
    for k in ("IF", "STATE seg A", "RT resume, state half", "STATE seg B", "finalize, state half"):
        if r[k]["in_equal"] and r[k]["out_equal"]:
            assert all(r[k]["checks"].values()), (k, r[k]["checks"])
        else:
            assert r[k]["m14_stale"], (k, r[k]["checks"])
    assert r["IF"]["d_in"] == r["STATE seg A"]["d_in"] and r["IF"]["d_out"] == r["finalize, state half"]["d_out"]
    assert r["WASM seg 0"]["in_equal"] and r["WASM seg 0"]["out_equal"] and r["WASM seg 1"]["in_equal"]
    # A-T5: the halting segment's out-record is lane A's `.fin r` record (finding I2b-2 closed), and
    # every in/out digest of the two Wasm leaves is the chain's (c4 -> c5 -> c6)
    assert r["WASM seg 1"]["out_equal"]
    assert all(r[f"WASM seg {k}"][f"d_{s}_equal"] for k in (0, 1) for s in ("in", "out"))
    # F-5: lane F's leaves are proved on the chain's records (enter c2 -> c3, resume c6 -> c7, the STATE
    # engine halves SE c1 -> c2, c7 -> c8, c8 -> c9): every in / out record equals the chain's
    for k in ("RT enter", "RT resume", "STATE seg A, engine half", "STATE seg B, engine half", "finalize, engine half"):
        if k in r:
            assert (r[k]["in_equal"] and r[k]["out_equal"]) or r[k]["m14_stale"], (k, r[k].get("diff_in"), r[k].get("diff_out"))
            # F-6 (lane D's F-M9-1): the whole boundary pair is in the proof, in one AIR, as bytes
            assert all(r[k]["checks"].values()), (k, r[k]["checks"])


@pytest.mark.skipif(not (HAVE_T1 and HAVE_LEAN), reason="T1 case or Lean v3 package absent")
def test_step_plan_fixture_fallback(tmp_path, monkeypatch):
    """`t1.py run`'s plan step on T1 without lane F's dump: the committed fixture stands in."""
    inp = t1_inputs()
    monkeypatch.setattr(chain, "LEAN_RUN", str(tmp_path / "absent.json"))
    calls = [{"prep": str(tmp_path / "prep.json"), "method": inp["call"]["method"], "prepaid": inp["call"]["prepaid"],
              "code_sha256": inp["call"]["code_sha256"], "steps": inp["call"]["steps"],
              "real": {"burnt": inp["call"]["burnt"], "used": inp["call"]["used"]}}]
    json.dump({"regularOpCost": inp["call"]["R"], "stackRem": inp["call"]["stackRem"], "g0": inp["call"]["g0"],
               "gFinal": inp["call"]["gFinal"]}, open(calls[0]["prep"], "w"))
    comps = {"state": {"bnd": {"pre_root": inp["prev_state_root"], "wsLen": inp["wsLen"]}},
             "wasm-seg": {"calls": [{"plan": True, "bnd": inp["segments"]}]}}
    full = {"outputs": {"stateRoot": inp["post_state_root"], "gasUsed": str(inp["gasUsed"]),
                        "balanceBurnt": str(inp["balanceBurnt"]), "computeUsage": str(inp["computeUsage"]),
                        "outcomes": [0] * inp["n_outcomes"], "outgoingReceipts": [0] * inp["n_outgoing"], "proposals": []}}
    t1.MISMATCHES.clear()
    r = t1.step_plan(str(tmp_path), bytes.fromhex(inp["claimDigest_S"]), full, calls, comps, T1_CASE)
    assert r["status"] == "pass" and r["digest_chain_ok"] and not t1.MISMATCHES, (r, t1.MISMATCHES)
    p = json.load(open(tmp_path / "plan.json"))
    assert [s["d_out"] for s in p["segments"]] == chain.digests(chain.build(inp))[1:]
