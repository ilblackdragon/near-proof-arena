#!/usr/bin/env python3
"""M10 driver skeleton for T1 (docs/zk-formal/E2E-T1-CRITICAL-PATH.md; plan §4 M10).

    t1.py run     CASE_DIR OUT_DIR [--steps K] [--prove]
    t1.py mutants CASE_DIR OUT_DIR [--jobs N]

`run`:
  1. extract     copy the case, split the claim into the D-2 public statement S (lane E's canonical
                 encoding, plan §3.4.1: claim-v3 with an empty section B) and the private section B;
                 claimDigest = bdigest(S); S and claimDigest checked byte for byte against a Lean
                 evaluation of `StmtEnc` (`lean/StmtEval.lean`), and for T1 against the
                 kernel-evaluated `t1_S_len` / `t1_claimDigest`;
  2. lean        the unmodified Lean checker (`--tier allFeatures`, then `--emit-full`): verdict,
                 self-check, outputs; FinalOut = header outputs vs the run's outputs;
  3. calls       the chunk's Wasm calls, twice: the Lean host tape (`wasmbase-tape`, or the cached
                 lane A M3 corpus tape when the exe is not built) and the clean-room checker
                 (`m1/extract_calls.py`, also writes the code blobs); cross-checked;
  4. components  run every component prover that exists today and read its **public boundary**:
                 lane A whole-call Wasm AIR (`wasmBaseM2Air`); lane A segment AIR
                 (`wasmBaseSegAirMP`: `segcheck`, `segdump` public values, Lean `HoldsX ∧ ChipIf`
                 on each dumped segment, `segprove`); lane B state (M5b AIR: `pubs.bin`, `TAPE`).
                 Each component boundary is compared with the Lean run's value where the Lean run
                 (checker output or Lean host tape) fixes it; a disagreement is a MISMATCH;
  5. plan        cut the run into lane E's T1 templates (`E2E/Templates.lean`: INIT, STATE, RT
                 enter, WASM per segment, RT resume, STATE, FINAL), fill each cut's `BndRec` from the
                 component boundaries (provenance per field: real / partial / placeholder), encode
                 with `bndrec.py`, check every cut against a Lean evaluation of `BndRec.encode` /
                 `bdigest`, and check the WASM cuts' chain independently (B_in(k) built from
                 segment k's own public values = B_out(k-1));
  6. report      OUT/report.json + OUT/report.md (per-component pass / fail / blocked / missing,
                 boundary checks). Exit status 1 on any MISMATCH (printed to stderr).

`mutants`: >= 50 mutants of S (one public field each: every chunk-header output field and every
trusted fact), all distinct, each re-assembled with the original private section B and witness and
run through the Lean checker; every decodable mutant's S / claimDigest is also evaluated in Lean.

Tools (env overrides): LEAN_CHECK, WASMBASE_TOOL, WASMBASE_TAPE, TAPE_JSONL, WB_PROVER, M5A_TOOL,
M5A_PROVER. Nothing here edits another lane's files; their scripts are run read-only.
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
MAIN = os.environ.get("NEARPROOF_MAIN", "/data/illia/nearproof")
DEPS = "/data/illia/nearproof-deps"
sys.path.insert(0, HERE)
import bndrec  # noqa: E402
import stmt  # noqa: E402

CHECKER_SHA = "644495ff5e04801f6ba206abb5d3f608bcfe0f10499767a8203464d4b10a9ae3"


def tool(env, default):
    return os.environ.get(env, default)


# every disagreement between a component's public boundary (or this driver's encoding) and the
# Lean run; printed to stderr and makes `run` exit 1
MISMATCHES = []


def mismatch(where, msg):
    MISMATCHES.append({"where": where, "msg": msg})
    print(f"MISMATCH [{where}] {msg}", file=sys.stderr, flush=True)


LEAN_CHECK = tool("LEAN_CHECK", f"{MAIN}/spec/lean/v3/.lake/build/bin/nearspec-v3-check-successor")
WASMBASE_TOOL = tool("WASMBASE_TOOL", f"{MAIN}/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tool")
WASMBASE_TAPE = tool("WASMBASE_TAPE", f"{MAIN}/research/near-compression/wasm-base-lean/.lake/build/bin/wasmbase-tape")
TAPE_JSONL = tool("TAPE_JSONL", f"{DEPS}/e2e-laneA/m3/tape.jsonl")
WB_PROVER = tool("WB_PROVER", f"{DEPS}/e2e-t1/target-wb/release/nearproof-wasm-base")
M5A_TOOL = tool("M5A_TOOL", f"{MAIN}/research/near-compression/e2e-general/m5a/lean/.lake/build/bin/m5a-tool")
M5A_PROVER = tool("M5A_PROVER", f"{DEPS}/e2e-t1/target-m5a/release/nearproof-e2e-m5a")
M1 = os.path.join(ROOT, "research/near-compression/e2e-general/m1")
M5A = os.path.join(ROOT, "research/near-compression/e2e-general/m5a")


def sha256f(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def sh(cmd, out=None, timeout=None, env=None):
    """Run a command (list), capture stdout+stderr to `out` (if given). Returns (rc, text, seconds)."""
    t0 = time.time()
    e = dict(os.environ)
    e.setdefault("RAYON_NUM_THREADS", "8")
    if env:
        e.update(env)
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout, env=e)
        rc, txt = p.returncode, p.stdout.decode(errors="replace")
    except subprocess.TimeoutExpired as x:
        rc, txt = -9, (x.stdout or b"").decode(errors="replace") + "\nTIMEOUT"
    if out:
        with open(out, "w") as f:
            f.write(txt)
    return rc, txt, time.time() - t0


def wjson(p, obj):
    with open(p, "w") as f:
        json.dump(obj, f, indent=1, sort_keys=False)
        f.write("\n")


# ---------------------------------------------------------------------------
# 1. extract
# ---------------------------------------------------------------------------
def step_extract(case, out):
    cdir = os.path.join(out, "case")
    os.makedirs(cdir, exist_ok=True)
    for f in ("claim.bin", "witness.bin", "meta.json"):
        shutil.copy(os.path.join(case, f), cdir)
    claim = open(os.path.join(case, "claim.bin"), "rb").read()
    pc = stmt.parse_claim(claim)
    s = stmt.statement_bytes(claim, pc)
    b0, b1 = pc["secB"]
    open(os.path.join(out, "S.bin"), "wb").write(s)
    open(os.path.join(out, "secB.bin"), "wb").write(claim[b0:b1])
    cd = stmt.claim_digest(s)
    pub = {k: v for k, v in pc.items() if k != "fields"}
    pub["S_len"], pub["S_sha256"], pub["claimDigest"] = len(s), hashlib.sha256(s).hexdigest(), cd.hex()
    pub["secB_bytes"] = b1 - b0
    pub["public_fields"] = [(f.name, f.sec, f.off, f.size, f.kind) for f in pc["fields"]]
    # the Lean evaluation of StmtEnc on the same claim bytes
    rows = stmt.lean_stmt([os.path.join(cdir, "claim.bin")])
    lean = stmt.lean_stmt_compare(claim, (rows or {}).get(os.path.join(cdir, "claim.bin")), pc)
    pub["lean_stmt"] = lean
    is_t1 = case_key(case) == "d3c8/d3/02-h10196-s3"
    t1_ok = None
    if is_t1:
        t1_ok = len(s) == stmt.T1_S_LEN and cd.hex() == stmt.T1_CLAIM_DIGEST
    wjson(os.path.join(out, "statement.json"), pub)
    meta = json.load(open(os.path.join(case, "meta.json")))
    ok = lean["ok"] and t1_ok is not False
    if not lean["ok"]:
        mismatch("statement", f"S / claimDigest differ from the Lean evaluation of StmtEnc: {lean}")
    if t1_ok is False:
        mismatch("statement", f"T1: |S| = {len(s)}, claimDigest {cd.hex()} != kernel-evaluated "
                 f"{stmt.T1_S_LEN} / {stmt.T1_CLAIM_DIGEST}")
    return {"status": "pass" if ok else "fail", "claimDigest": cd.hex(), "S_len": len(s),
            "stmtPre_len": b0, "stmtPost_len": len(s) - b0 - 4,
            "secB_bytes": b1 - b0, "lean_stmt_equal": lean["ok"], "t1_kernel_values_equal": t1_ok,
            "n_public_fields": len(pc["fields"]), "meta_expected_rel": meta.get("expected_rel"),
            "meta_nearcore": meta.get("nearcore")}, pc, cd


# ---------------------------------------------------------------------------
# 2. Lean checker
# ---------------------------------------------------------------------------
def step_lean(case, out, pc):
    got = sha256f(LEAN_CHECK)
    rc, txt, dt = sh([LEAN_CHECK, "--tier", "allFeatures", case], os.path.join(out, "lean-verdict.json"))
    v = json.loads(txt.strip().splitlines()[-1])
    rc2, txt2, dt2 = sh([LEAN_CHECK, "--tier", "allFeatures", "--emit-full", case])
    open(os.path.join(out, "lean-full.json"), "w").write(txt2)
    full = json.loads(txt2)
    fo = stmt.final_out_table(pc, full["outputs"])
    wjson(os.path.join(out, "finalout.json"), fo)
    ok = (got == CHECKER_SHA and v["verdict"] == "accept" and full["verdict"] == "accept"
          and all(full["selfCheck"].values()) and all(r["equal"] for r in fo))
    return {"status": "pass" if ok else "fail", "checker_sha256": got, "checker_pinned": got == CHECKER_SHA,
            "verdict": v["verdict"], "reason": v["reason"], "selfCheck": full["selfCheck"],
            "finalout_rows": len(fo), "finalout_equal": sum(r["equal"] for r in fo),
            "seconds": round(dt + dt2, 2)}, full


# ---------------------------------------------------------------------------
# 3. the chunk's Wasm calls (Lean tape + clean-room)
# ---------------------------------------------------------------------------
def case_key(case):
    return "/".join(os.path.abspath(case).rstrip("/").split("/")[-3:])


def step_calls(case, out):
    cdir = os.path.join(out, "calls")
    os.makedirs(os.path.join(cdir, "codes"), exist_ok=True)
    key = case_key(case)
    if os.path.exists(WASMBASE_TAPE):
        src = "wasmbase-tape (fresh)"
        tape_path = os.path.join(cdir, "tape.jsonl")
        sh([WASMBASE_TAPE, tape_path, case], os.path.join(cdir, "tape.log"))
        lines = [json.loads(x) for x in open(tape_path)]
    else:
        src = f"cached lane A M3 corpus tape {TAPE_JSONL} (sha256 {sha256f(TAPE_JSONL)[:16]}…); wasmbase-tape not built"
        lines, cur = [], None
        with open(TAPE_JSONL) as f:
            for ln in f:
                d = json.loads(ln)
                if "case" in d:
                    cur = d["case"]
                    if cur.endswith(key) and "verdict" in d:
                        lines.append(d)
                    continue
                if cur and cur.endswith(key):
                    lines.append(d)
    tape = [d for d in lines if "seq" in d]
    verdicts = [d for d in lines if "verdict" in d]
    rc, txt, _ = sh([sys.executable, os.path.join(M1, "extract_calls.py"), case, "--code-dir",
                     os.path.join(cdir, "codes")], os.path.join(cdir, "cleanroom.json"))
    clean = json.loads(txt) if rc == 0 else {"calls": []}
    calls, agree = [], True
    for i, t in enumerate(tape):
        c = clean["calls"][i] if i < len(clean["calls"]) else {}
        prep_path = os.path.join(cdir, f"{i:02d}.prep.json")
        if t.get("prep", {}).get("eligible"):
            wjson(prep_path, t["prep"])
        same = (c.get("code_sha256") == t["code_sha256"] and c.get("method") == t["method"]
                and c.get("burnt") == t["real"]["burnt"])
        agree &= same
        calls.append({"index": i, "code_sha256": t["code_sha256"], "method": t["method"],
                      "prepaid": t["prepaid"], "input": t["input"], "real": t["real"],
                      "steps": t.get("prep", {}).get("steps"), "eligible": t.get("prep", {}).get("eligible"),
                      "replayMatches": t.get("replayMatches"), "cleanroom_agrees": same,
                      "prep": prep_path if t.get("prep", {}).get("eligible") else None,
                      "wasm": os.path.join(cdir, "codes", t["code_sha256"] + ".wasm")})
    wjson(os.path.join(cdir, "calls.json"), calls)
    st = "pass" if tape and agree and all(c["replayMatches"] for c in calls) else "fail"
    return {"status": st, "source": src, "n_calls": len(calls), "tape_verdict": [v["verdict"] for v in verdicts],
            "cleanroom_verdict": clean.get("verdict"), "lean_vs_cleanroom_agree": agree}, calls


# ---------------------------------------------------------------------------
# 5. the segment plan: lane E's T1 templates, each cut a BndRec filled from the components
# ---------------------------------------------------------------------------
# Templates.lean (`NearSpecV3.E2E.T1.Tmpl`) and the lane that owns each premise (plan §3.5)
TMPL_OWNER = {"INIT": "G (SegSoundInit)", "STATE": "B (SegSoundState)", "RT": "F (SegSoundRt)",
              "WASM": "A (SegSoundWasm)", "FINAL": "G (SegSoundFinal)"}
# lane I's I-1 7-segment plan -> the templates (plan §3.5, cm_decomp)
I1_MAP = [("INTAKE", "INIT"), ("STATE(r0)", "STATE (every VM-free engine step up to receipt 1's step)"),
          ("STATE(r1 up to VM call)", "RT enter"), ("WASM(0,13] WASM(13,26]", "WASM (cuts anywhere: MWasm)"),
          ("STATE(r1 resume)", "RT resume"), ("(inside FINAL)", "STATE (VM-free engine steps after receipt 1, to eng done)"),
          ("FINAL", "FINAL")]

ZERO48 = b"\x00" * 48


def st_partial(tag, st_bnd):
    """lane B's state commitment in its circuit form (`StateM5a.StateView.stD`: `bdigest (ser
    StCommit)`, `ser = [tag] ‖ ws(48) ‖ u64le wsLen ‖ trie(32) ‖ u64le idx ‖ rest(42)`) with the
    fields M5b exposes publicly (`trie` = prev_state_root: the overlay never modifies the trie before
    FINAL; `wsLen`) and placeholders for the rest (`ws` = the RCH root and `rest` = the remainder
    digest are not public; `idx` = 0, lane E M11i item 5)."""
    ser = bytes([tag]) + ZERO48 + st_bnd["wsLen"].to_bytes(8, "little") + bytes.fromhex(st_bnd["pre_root"]) \
        + (0).to_bytes(8, "little") + bndrec.ZERO
    return bndrec.bdigest(ser)


def wasm_of(b):
    """lane A's `WasmView.airBnd` from one side of a segment's public boundary (`segdump` publics):
    pc = global pc, sp = sb, framesDigest = globalsDigest = registersDigest = ctxDigest[:42],
    memRoot = memRoot[:42], memPages = nblk / 64, promisesDigest = bdigest []. Not public (placeholders):
    stackRem, fuel (the call machine's `n`), vmCtxDigest (bdigest of lane E's `encRest`), codeRoot /
    funcRoot (`P.codeRootOf`; the proof's CODE/FUNC commitments are checked natively, not exposed)."""
    w = bndrec.wasm_blank()
    fd = bytes.fromhex(b["ctx"])[:42]
    w.update(pc=b["pc"], sp=b["sb"], framesDigest=fd, globalsDigest=fd, registersDigest=fd,
             memRoot=bytes.fromhex(b["mem"])[:42], memPages=b["nblk"] // 64, promisesDigest=bndrec.bdigest(b""))
    return w


WASM_REAL = ["pc", "sp", "framesDigest", "memRoot", "memPages", "globalsDigest", "registersDigest", "promisesDigest"]


def step_plan(out, cd, full, calls, comps, k_steps):
    """Cut the run into the T1 templates and fill each cut's BndRec.

    Clear fields: phase (`View.split` tags), receipt index, cumulative gas/compute (the Lean run's
    outcomes), `t` (lane A's in-call clock). Digests: `claimDigest` (statement, Lean-checked), `stRoot`
    (lane B public values, partial StCommit), `wasm` (lane A segment publics); every other digest is a
    0^42 placeholder (`provenance` says which, `producer` who must fill it)."""
    o = full["outputs"]
    outcomes = o["outcomes"]
    st = comps.get("state", {}).get("bnd")
    wsegs = {c["call"]: c for c in comps.get("wasm-seg", {}).get("calls", []) if c.get("plan")}
    segs = []
    rec = bndrec.blank(cd)
    rec["phase"] = bndrec.PHASE["init"]
    prov_st = "partial: lane B M5b public (trie = prev_state_root, wsLen); ws/rest placeholders" if st else "placeholder"

    def cut(template, what, **upd):
        nonlocal rec
        b_in = rec
        b_out = dict(rec)
        b_out.update(upd)
        segs.append({"template": template, "owner": TMPL_OWNER[template.split()[0]], "what": what,
                     "B_in": b_in, "B_out": b_out})
        rec = b_out

    eng_st = st_partial(1, st) if st else bndrec.ZERO
    cut("INIT", "init cb wb -> eng I start (CM.step: decode claim + witness, intake; M5b INTAKE: pre-state trie)",
        phase=bndrec.PHASE["eng"], stRoot=eng_st)
    gas = burnt = comp = 0
    call_by_exec = {c["index"]: c for c in calls}
    ci = 0
    pending = []   # VM-free receipts not yet closed into a STATE segment
    seams = []
    for ri, oc in enumerate(outcomes):
        has_call = bool(oc["logs"]) or oc["status"]["kind"] == "value"
        g, cu = int(oc["gasBurnt"]), int(oc["computeUsage"])
        ex = bytes.fromhex(oc["executor"]).decode()
        if not (has_call and ci in call_by_exec):
            gas, burnt, comp = gas + g, burnt + g, comp + cu
            pending.append(f"r{ri} {ex} ({oc['status']['kind']})")
            continue
        c = call_by_exec[ci]
        ci += 1
        cut("STATE", "VM-free engine steps: " + (", ".join(pending) or "start") + f"; up to receipt {ri}'s step",
            receiptIdx=ri, gasUsed=gas, gasBurnt=burnt, compute=comp)
        pending = []
        ws = wsegs.get(c["index"], {})
        bnds = ws.get("bnd") or []
        w0 = wasm_of(bnds[0]["in"]) if bnds else bndrec.wasm_blank()
        cut("RT enter", f"receipt {ri} ({ex}): enter call {c['index']} {c['method']} (eng I c -> call I c [] q .pre)",
            phase=bndrec.PHASE["call"], inCall=True, wasm=w0, rPrepaid=c["prepaid"], t=0)
        if bnds:
            seams.append(f"call {c['index']}: RT enter ends at `.pre` (lane A WasmView: fbBnd), lane A's segment 0 "
                         "starts at the entry state (airBnd); the `.pre -> .ent` step (PREP, C7) is in no AIR. "
                         "The plan puts segment 0's entry boundary at the RT enter cut.")
        steps = c["steps"] or 0
        if bnds:
            for k, b in enumerate(bnds):
                # the chain, independently: B_in(k) from segment k's own publics = B_out(k-1)
                w_in = wasm_of(b["in"])
                if w_in != rec["wasm"] or b["in"]["t"] != rec["t"]:
                    mismatch("plan", f"call {c['index']} WASM segment {k}: B_in from its own public values "
                             f"!= B_out of the previous cut")
                cut("WASM", f"call {c['index']} {c['method']} steps ({b['in']['t']}, {b['out']['t']}] of {steps}"
                    f"{' (halts)' if b['halted'] else ''}: lane A wasmBaseSegAirMP segment {k}",
                    t=b["out"]["t"], wasm=wasm_of(b["out"]))
        else:
            t = 0
            while t < steps:
                t2 = min(steps, t + k_steps)
                cut("WASM", f"call {c['index']} {c['method']} steps ({t}, {t2}] of {steps} (no segment boundary)", t=t2)
                t = t2
        gas, burnt, comp = gas + g, burnt + g, comp + cu
        cut("RT resume", f"receipt {ri}: the receipt step with the VM answered from the tape (refund, outcome)",
            phase=bndrec.PHASE["eng"], inCall=False, wasm=None, gasUsed=gas, gasBurnt=burnt, compute=comp,
            rBurnt=int(c["real"]["burnt"]), rUsed=int(c["real"]["used"]))
    cut("STATE", "VM-free engine steps: " + (", ".join(pending) or "(none of the outcomes)")
        + " -> eng I <done out> (yields, delayed queue, ...)", gasUsed=gas, gasBurnt=burnt, compute=comp)
    cut("FINAL", "eng done -> fin -> done H o: implicit transitions, outputs, headerOk (M5b FINAL: post-state root)",
        phase=bndrec.PHASE["done"], stRoot=bndrec.ZERO)
    # encode every cut, check the chain as digests and every record against Lean
    chain_ok = True
    for i, s in enumerate(segs):
        s["d_in"], s["d_out"] = bndrec.digest(s["B_in"]).hex(), bndrec.digest(s["B_out"]).hex()
        if i and segs[i - 1]["d_out"] != s["d_in"]:
            chain_ok = False
    recs = [segs[0]["B_in"]] + [s["B_out"] for s in segs]
    ldir = os.path.join(out, "lean-bnd")
    os.makedirs(ldir, exist_ok=True)
    lc = bndrec.lean_check(recs, ldir)
    if lc["ok"] is not True:
        mismatch("plan", f"BndRec encode/bdigest differ from the Lean evaluation (or Lean not run): "
                 f"{lc.get('error') or [i for i, r in enumerate(lc['rows']) if not (r['encode_equal'] and r['digest_equal'])]}")
    gas_ok = gas == int(o["gasUsed"]) and comp == int(o["computeUsage"])
    if not gas_ok:
        mismatch("plan", f"sum of outcome gas/compute {gas}/{comp} != Lean gasUsed/computeUsage")
    prov = {"claimDigest": "real: bdigest(S), S = StmtEnc (Lean-checked)",
            "phase/receiptIdx/inCall/gasUsed/gasBurnt/compute/rPrepaid/rBurnt/rUsed": "clear: the Lean run's outcomes",
            "t": "clear: lane A's in-call clock (segment publics) inside a call, else 0",
            "stRoot": prov_st,
            "wasm." + "/".join(WASM_REAL): "real: lane A segment publics (WasmView.airBnd)" if wsegs else "placeholder",
            "wasm.stackRem/fuel/vmCtxDigest/codeRoot/funcRoot": "placeholder (not in lane A's public values)",
            "ctxRoot/outcomeAcc/outRcptAcc/proposalsAcc/bwAcc/vmAcc/balanceBurnt/blockIdx/actionIdx":
                "placeholder (no component: lanes F/G, A/E)"}
    j = [{"index": i, "template": s["template"], "owner": s["owner"], "what": s["what"],
          "d_in": s["d_in"], "d_out": s["d_out"], "lean_d_out": lc["rows"][i + 1]["digest"] if lc.get("rows") else None,
          "B_out": bndrec.to_json(s["B_out"])} for i, s in enumerate(segs)]
    wjson(os.path.join(out, "plan.json"), {"segments": j, "B_0": bndrec.to_json(segs[0]["B_in"]),
                                           "provenance": prov, "seams": seams, "i1_mapping": I1_MAP,
                                           "placeholder_fields": bndrec.PRODUCER,
                                           "lean_bndrec": {k: v for k, v in lc.items() if k != "rows"}})
    ok = chain_ok and gas_ok and lc["ok"] is True
    return {"status": "pass" if ok else "fail", "n_segments": len(segs),
            "templates": [s["template"] for s in segs], "digest_chain_ok": chain_ok,
            "lean_bndrec_equal": lc["ok"], "lean_bndrec_records": lc.get("n"),
            "record_bytes": sorted({r["len"] for r in lc.get("rows", [])}),
            "gas_compute_sum_equals_header": gas_ok, "complete": False, "provenance": prov, "seams": seams,
            "note": "digests real where a component publishes the field; the rest are 0^42 placeholders"}


# ---------------------------------------------------------------------------
# 4. components
# ---------------------------------------------------------------------------
def nloc_ngl(prep):
    p = json.load(open(prep))
    return len(p["localTags"]), p["ngl"]


def comp_wasm_call(out, calls, prove):
    """Lane A, whole call, `wasmBaseM2Air` (no boundary): trace from the chunk's tape, pre-check,
    compare with the chunk's outcome; optionally prove + verify."""
    d = os.path.join(out, "wasm-call")
    os.makedirs(d, exist_ok=True)
    res = []
    for c in calls:
        if not c["prep"]:
            res.append({"call": c["index"], "status": "missing", "why": "not eligible for checkModuleM2"})
            continue
        nl, ng = nloc_ngl(c["prep"])
        air = os.path.join(d, f"airM2-{nl}-{ng}.json")
        sh([WASMBASE_TOOL, "airM2", str(nl), str(ng)], air)
        rc, txt, _ = sh([WB_PROVER, "check-tape", air, c["prep"]], os.path.join(d, f"{c['index']:02d}.check-tape.json"))
        ct = json.loads(txt.strip().splitlines()[-1]) if rc == 0 else {"ok": False, "err": txt[-300:]}
        p = json.load(open(c["prep"]))
        # burnt = preSync.burnt + preSync.remaining - g_final_trace (m3/sweep.py); preSync from the tape
        eq_ret = ct.get("rets", [None])[-1:] == [c["real"]["ret"]]
        eq_logs = ct.get("logs") == c["real"]["logs"]
        eq_gas = ct.get("g_final_trace") == p["gFinal"]
        rc2, txt2, _ = sh([WB_PROVER, "check", air, c["prep"]], os.path.join(d, f"{c['index']:02d}.check.log"))
        r = {"call": c["index"], "check_tape_ok": ct.get("ok"), "check_ok": "CHECK OK" in txt2,
             "return_equal": eq_ret, "logs_equal": eq_logs, "gfinal_equal_tape": eq_gas}
        if prove and r["check_ok"]:
            rc3, txt3, dt = sh([WB_PROVER, "prove", air, c["prep"], "small"], os.path.join(d, f"{c['index']:02d}.prove.log"),
                               env={"WASMBASE_WASM": c["wasm"], "WASMBASE_PROOF_OUT": os.path.join(d, f"{c['index']:02d}.proof.bin")})
            # `prove` verifies natively (`eng.verify(..).expect`) and re-checks code_root before PROVE OK
            m = re.search(r"PROOF total=(\d+)", txt3)
            tv = re.search(r"prove ([0-9.]+)s verify ([0-9.]+)s", txt3)
            ch = re.search(r"code_hash ([0-9a-f]{64})", txt3)
            r.update(prove_rc=rc3, verified="PROVE OK" in txt3, proof_bytes=int(m.group(1)) if m else None,
                     prove_s=float(tv.group(1)) if tv else round(dt, 1), verify_s=float(tv.group(2)) if tv else None,
                     code_hash=ch.group(1) if ch else None, code_root_checked_natively="code_root" in txt3)
        r["status"] = "pass" if all(r[k] for k in ("check_tape_ok", "check_ok", "return_equal", "logs_equal")) \
            and (not prove or r.get("verified")) else "fail"
        res.append(r)
    st = "pass" if res and all(x["status"] == "pass" for x in res) else ("missing" if not res else "fail")
    return {"status": st, "air": "wasmBaseM2Air (no segment boundary; HOSTO oracle answers host calls)", "calls": res}


# ---------------------------------------------------------------------------
# lane A segment AIR: public boundary (`segdump` publics; layout `Seg.pub*`, SegAir.lean / seg.rs)
# ---------------------------------------------------------------------------
SEG_RE = re.compile(r"segment (\d+): (.*)")
PUB = {"halted": 8, "memsize": 9, "in": 11, "out": 21, "ctx_in": 31, "ctx_out": 49, "mem_in": 67, "mem_out": 85,
       "depth": 103, "nblk": 104}
STORE_OPS = set(range(0x36, 0x3f)) | {0x40}   # Wasm stores and memory.grow (record opcode field)


def read_pubs(path):
    """The public values of a `dump.rs` file (`NPTD` v1: magic, version, npub, pub[npub], ...)."""
    import struct
    b = open(path, "rb").read(12)
    magic, ver, n = struct.unpack("<3I", b)
    assert magic == 0x4454504E and ver == 1, "not an NPTD v1 dump"
    with open(path, "rb") as f:
        f.seek(12)
        return list(struct.unpack(f"<{n}I", f.read(4 * n)))


def _dig48(p, off):
    """6 SHA-512 words as 3 limbs each (`seg::wl`: 21 + 21 + 22 bits), big-endian bytes."""
    return b"".join((p[off + 3 * j] + (p[off + 3 * j + 1] << 21) + (p[off + 3 * j + 2] << 42)).to_bytes(8, "big")
                    for j in range(6)).hex()


def seg_bnd(p, R):
    """Both sides of a segment's public boundary: `pc, t, S, sb, cid, S_seg, segb` (16-bit limbs),
    ctxDigest, memRoot (48 B), D, nblk; the gas `g = segb - R (S - S_seg)` (SegAir.lean)."""
    def side(base, ctx, mem):
        pc, t, S, sb, cid, sseg = p[base:base + 6]
        segb = sum(p[base + 6 + i] << (16 * i) for i in range(4))
        return {"pc": pc, "t": t, "S": S, "sb": sb, "cid": cid, "S_seg": sseg, "segb": segb,
                "g": segb - R * (S - sseg), "ctx": _dig48(p, ctx), "mem": _dig48(p, mem),
                "nblk": p[PUB["nblk"]], "depth": p[PUB["depth"]]}
    return {"in": side(PUB["in"], PUB["ctx_in"], PUB["mem_in"]), "out": side(PUB["out"], PUB["ctx_out"], PUB["mem_out"]),
            "halted": p[PUB["halted"]], "memsize": p[PUB["memsize"]]}


def _sha384(b):
    return hashlib.sha384(b).digest()


def mem_root(mem, nblk):
    """lane A's memory Merkle root (`WasmView.memRootOf`, `seg.rs` `Tree`): leaves = SHA-384 of each
    1 KiB block in address order, node = SHA-384(l ‖ r), depth `bitlen(max(nblk, 2) - 1)`; sparse
    (zero subtrees by `Z_{k+1} = H(Z_k ‖ Z_k)`)."""
    d = max(1, (max(nblk, 2) - 1).bit_length())
    z = [_sha384(bytes(1024))]
    for k in range(d):
        z.append(_sha384(z[k] + z[k]))
    blocks = {}
    for a, v in mem.items():
        blocks.setdefault(a // 1024, bytearray(1024))[a % 1024] = v
    level = {i: _sha384(bytes(b)) for i, b in blocks.items()}
    for k in range(d):
        level = {i: _sha384(level.get(2 * i, z[k]) + level.get(2 * i + 1, z[k])) for i in {x // 2 for x in level}}
    return level.get(0, z[d]).hex()


def lean_ref_mem(prep):
    """The memory the Lean run fixes: the initial image (Lean `prep`: `data[0:dataEnd]`) and, when the
    code has no store / memory.grow record, the final memory = image + the `read_register` writes of
    the Lean host tape (`hosts`: hid 49, args [register, ptr], register file at the call)."""
    m0 = {a: v for a, v in enumerate(prep["data"][:prep["dataEnd"]]) if v}
    store_free = not any(r[1] in STORE_OPS for r in prep["records"])
    m1 = None
    if store_free:
        m1 = dict(m0)
        for h in prep["hosts"]:
            if h["hid"] == 49:
                regs = dict((r[0], r[1]) for r in h["regs"])
                for i, x in enumerate(regs.get(h["args"][0], [])):
                    m1[h["args"][1] + i] = x
        m1 = {a: v for a, v in m1.items() if v}
    return m0, m1, store_free


def wasm_lean_checks(c, prep, bnds, k):
    """Compare a call's segment boundaries with the Lean run's values (Lean prep + host tape)."""
    rows = []

    def chk(what, got, want):
        rows.append({"check": what, "component": got, "lean": want, "equal": got == want})
        if got != want:
            mismatch("wasm-seg", f"call {c['index']} {what}: component {got} != Lean {want}")
    nblk = prep["mem"] // 1024
    m0, m1, store_free = lean_ref_mem(prep)
    b0, bl = bnds[0], bnds[-1]
    chk("segment 0 B_in t", b0["in"]["t"], 0)
    chk("segment 0 B_in pc (entry fn's first instruction)", b0["in"]["pc"], prep["funcs"][prep["fn"]][0])
    chk("segment 0 B_in S, sb, cid", (b0["in"]["S"], b0["in"]["sb"], b0["in"]["cid"]), (0, 0, 0))
    chk("segment 0 B_in gas g (= prep g0)", b0["in"]["g"], prep["g0"])
    chk("memory size (bytes)", b0["memsize"], prep["mem"])
    chk("nblk (= 64 pages)", b0["in"]["nblk"], nblk)
    chk("memory depth D", b0["in"]["depth"], max(1, (max(nblk, 2) - 1).bit_length()))
    chk("segment 0 B_in memRoot (Merkle root of the Lean prep image)", b0["in"]["mem"], mem_root(m0, nblk))
    for i, b in enumerate(bnds):
        chk(f"segment {i} B_out t", b["out"]["t"], min(prep["steps"], (i + 1) * k))
        chk(f"segment {i} halted", b["halted"], int(i == len(bnds) - 1))
        if i:
            chk(f"chain: segment {i} B_in = segment {i - 1} B_out (publics)", b["in"], bnds[i - 1]["out"])
    chk("last B_out gas g (= Lean tape gFinal)", bl["out"]["g"], prep["gFinal"])
    if prep["hosts"]:
        chk("last B_out gas g (= last host call's gAfter, Lean tape)", bl["out"]["g"], prep["hosts"][-1]["gAfter"])
    if store_free:
        chk("last B_out memRoot (image + read_register writes, Lean host tape)", bl["out"]["mem"], mem_root(m1, nblk))
    else:
        rows.append({"check": "last B_out memRoot", "component": bl["out"]["mem"], "lean": None, "equal": None,
                     "note": "code stores to memory: no Lean reference without the interpreter"})
    return rows


def comp_wasm_seg(out, calls, ks, prove):
    """Lane A segment AIR `wasmBaseSegAirMP`: for each cut size k, cut the call every k steps,
    `segcheck` (pre-check + lane A's chain), and at the plan's k (`ks[0]`): `segdump` (the public
    values every segment proof exposes, `statement_ok`), the boundary checks against the Lean run,
    the Lean `HoldsX ∧ ChipIf` checker on each dumped segment (`wasmbase-tool holds`), and with
    --prove `segprove`."""
    d = os.path.join(out, "wasm-seg")
    os.makedirs(d, exist_ok=True)
    seg_air = os.path.join(d, "airSegMP.json")
    sh([WASMBASE_TOOL, "airSegMP", "0", "0"], seg_air)
    res = []
    for c in calls:
        if not c["prep"]:
            continue
        prep = json.load(open(c["prep"]))
        nl, ng = nloc_ngl(c["prep"])
        air = os.path.join(d, f"airM2-{nl}-{ng}.json")
        sh([WASMBASE_TOOL, "airM2", str(nl), str(ng)], air)
        for ki, k in enumerate(ks):
            rc, txt, dt = sh([WB_PROVER, "segcheck", seg_air, air, c["prep"], str(k)],
                             os.path.join(d, f"{c['index']:02d}.segcheck-k{k}.log"))
            nseg = len(re.findall(r"^SEG \d+ ", txt, re.M))
            pre_ok = len(re.findall(r"PRECHECK OK", txt))
            chained = "SEGCHECK OK" in txt
            m = SEG_RE.search(txt)
            r = {"call": c["index"], "steps": c["steps"], "k": k, "segments": nseg, "precheck_ok": pre_ok,
                 "chained": chained, "error": m.group(0)[:300] if m else None, "plan": ki == 0}
            if chained and ki == 0:
                base = os.path.join(d, f"{c['index']:02d}.k{k}")
                rc2, txt2, _ = sh([WB_PROVER, "segdump", seg_air, air, c["prep"], str(k), base],
                                  os.path.join(d, f"{c['index']:02d}.segdump-k{k}.log"))
                dumps = [f"{base}-{i}.bin" for i in range(nseg)]
                if "SEGDUMP OK" in txt2 and all(os.path.exists(x) for x in dumps):
                    r["bnd"] = [seg_bnd(read_pubs(x), prep["regularOpCost"]) for x in dumps]
                    r["n_public_values"] = len(read_pubs(dumps[0]))
                    r["lean_checks"] = wasm_lean_checks(c, prep, r["bnd"], k)
                    r["lean_checks_equal"] = all(x["equal"] is not False for x in r["lean_checks"])
                    hx = []
                    for i, x in enumerate(dumps):
                        rc3, txt3, dt3 = sh([WASMBASE_TOOL, "holds", "segMP", "0", "0", x],
                                            os.path.join(d, f"{c['index']:02d}.holds-k{k}-{i}.log"))
                        hx.append({"segment": i, "HoldsX_ChipIf": "RESULT HoldsX ∧ ChipIf compressW (segMP 0 0): SATISFIED" in txt3,
                                   "seconds": round(dt3, 1)})
                        if not hx[-1]["HoldsX_ChipIf"]:
                            mismatch("wasm-seg", f"call {c['index']} segment {i}: Lean HoldsX ∧ ChipIf not satisfied")
                        os.remove(x)   # dumps are ~6 MB each
                    r["lean_holds"] = hx
                else:
                    r["segdump_error"] = txt2[-300:]
                    mismatch("wasm-seg", f"call {c['index']}: segdump failed")
                if prove:
                    rc4, txt4, dt4 = sh([WB_PROVER, "segprove", seg_air, air, c["prep"], str(k)],
                                        os.path.join(d, f"{c['index']:02d}.segprove-k{k}.log"),
                                        env={"WASMBASE_WASM": c["wasm"]})
                    pr = [{"proof_bytes": int(a), "prove_s": float(b), "verify_ms": int(v)} for a, b, v in
                          re.findall(r"PROOF \d+: (\d+) B, prove ([0-9.]+)s, verify (\d+) ms, statement ok", txt4)]
                    r.update(segprove_ok="SEGPROVE OK" in txt4, proofs=pr, prove_s=round(dt4, 1))
            if chained and (not prove or ki or r.get("segprove_ok")) and r.get("lean_checks_equal", True) \
                    and all(h["HoldsX_ChipIf"] for h in r.get("lean_holds", [])):
                r["status"] = "pass"
            elif m and "unbalanced" in m.group(2):
                r["status"] = "blocked"
            else:
                r["status"] = "fail"
            res.append(r)
    st = "pass" if res and all(x["status"] == "pass" for x in res) else \
        ("blocked" if any(x["status"] == "blocked" for x in res) else ("missing" if not res else "fail"))
    return {"status": st, "air": "wasmBaseSegAirMP (M4c default segment AIR)", "calls": res}


def comp_state(case, out, full, prove, d_ws=5):
    """Lane B: M5b AIR (INTAKE + working set + STATE write rows + FINAL MPT root) on the chunk's main
    transition, through lane B's own scripts (run read-only). Public boundary: `pubs.bin`
    (prev_state_root, wsLen) and `TAPE` (the root chain's ends `(0, pre)`, `(n, post)`, verifier-
    committed), compared with the Lean run (state root, write count) and the clean-room pre-state."""
    import struct
    d = os.path.join(out, "state")
    os.makedirs(d, exist_ok=True)
    shutil.copy(os.path.join(out, "lean-full.json"), os.path.join(d, "lean-full.json"))
    r = {}
    rc, txt, _ = sh([sys.executable, os.path.join(M5A, "extract_state.py"), case, os.path.join(d, "lean-full.json"),
                     os.path.join(d, "state.json")], os.path.join(d, "extract.log"))
    if rc:
        mismatch("state", "extract_state failed")
        return {"status": "fail", "step": "extract_state", "tail": txt[-400:]}
    sh([M5A_TOOL, "airb", str(d_ws), os.path.join(d, "m5b.json"), os.path.join(d, "names.json")], os.path.join(d, "air.txt"))
    rc, got, _ = sh([M5A_TOOL, "apply", os.path.join(d, "state.json")])
    stj = json.load(open(os.path.join(d, "state.json")))
    want = stj["post_root"]
    r["spec_oracle_root"] = got.strip()
    r["post_root_equal_header"] = got.strip() == want == full["outputs"]["stateRoot"]
    rc, txt, _ = sh([sys.executable, os.path.join(M5A, "tracegen.py"), os.path.join(d, "state.json"),
                     os.path.join(d, "names.json"), os.path.join(d, "dump")], os.path.join(d, "gen.txt"))
    if rc:
        mismatch("state", "tracegen failed")
        return {"status": "fail", "step": "tracegen", "tail": txt[-400:], **r}
    # the public boundary
    pb = open(os.path.join(d, "dump", "pubs.bin"), "rb").read()
    pubs = struct.unpack(f"<{len(pb) // 4}I", pb)
    limbs = lambda xs: b"".join(int(x).to_bytes(2, "big") for x in xs).hex()  # noqa: E731
    tape = json.load(open(os.path.join(d, "dump", "tape.json")))
    roots = [(m[2][0], limbs(m[2][2:18])) for m in tape if m[1] is True or m[1] is False]
    bnd = {"pre_root": limbs(pubs[:16]), "wsLen": pubs[16], "tape_root_chain": roots}
    r["bnd"] = bnd
    rows = []

    def chk(what, got_, want_, ref):
        rows.append({"check": what, "component": got_, "reference": want_, "ref": ref, "equal": got_ == want_})
        if got_ != want_:
            mismatch("state", f"{what}: component {got_} != {ref} {want_}")
    o = full["outputs"]
    chk("pubs prev_state_root = TAPE (0, root)", bnd["pre_root"], roots[0][1] if roots else None, "TAPE")
    chk("TAPE first index", roots[0][0] if roots else None, 0, "TAPE")
    chk("TAPE (n, post_state_root): root", roots[-1][1] if roots else None, o["stateRoot"], "Lean stateRoot")
    chk("TAPE (n, post_state_root): n", roots[-1][0] if roots else None, len(o["stateChanges"]), "Lean |stateChanges|")
    chk("prev_state_root", bnd["pre_root"], stj["pre_root"], "clean-room checker (no Lean output)")
    chk("wsLen", bnd["wsLen"], len(stj["keys_read"]), "clean-room keys read (no Lean output)")
    r["boundary_checks"] = rows
    r["boundary_equal"] = all(x["equal"] for x in rows)
    mode = "prove" if prove else "check"
    rc, txt, dt = sh([M5A_PROVER, os.path.join(d, "m5b.json"), os.path.join(d, "dump"), mode], os.path.join(d, f"{mode}.log"))
    r["precheck_ok"] = "PRECHECK OK" in txt
    if prove:
        m = re.search(r"proof_bytes (\d+)", txt)
        tv = re.search(r"TIME prove ([0-9.]+)s verify ([0-9.]+)s", txt)
        r.update(verified="VERIFY OK" in txt, proof_bytes=int(m.group(1)) if m else None,
                 prove_s=float(tv.group(1)) if tv else round(dt, 1), verify_s=float(tv.group(2)) if tv else None)
    ok = r["post_root_equal_header"] and r["precheck_ok"] and r["boundary_equal"] and (not prove or r["verified"])
    r["status"] = "pass" if ok else "fail"
    r["air"] = f"M5b (m5a-tool airb {d_ws}); host requests from the public HTAPE (not yet lane A's HOST rows)"
    return r


MISSING = [
    ("intake (INIT)", "G", "claim + witness decoding in-circuit, receipt intake, INIT leaf: B_0 = Init(claimDigest) -> eng I start with ctxRoot = ctxD(I) (SegSoundInit)"),
    ("receipt step (RT enter/next/resume)", "F", "FunctionCall action, refund, outcome, gas/compute counters around the VM call, VM answered from the tape K (SegSoundRt)"),
    ("VM-free engine steps (STATE)", "B (+F)", "STATE leaves: the forward receipt, queue/yield steps, as split leaves exposing stRoot = stD(StV) (SegSoundState); M5b today is one INIT..FINAL proof"),
    ("join-M6", "A + B", "HOSTQ/HOSTR/HOSTB produced by STATE rows in the WASM segment's trace (HostIf); HOSTO oracle removed"),
    ("prep", "unassigned", "PREP: `.pre -> .ent` (SHA-256(code) = code hash, checkModuleM2 + instrumentation -> CODE/FUNC roots = wasm.codeRoot/funcRoot)"),
    ("finalout (FINAL)", "G", "outcome root, outgoing receipts root, congestion, bandwidth requests, RS encoded_merkle_root/length, tx root; FINAL leaf checks headerOk vs S (SegSoundFinal)"),
    ("leaves", "A/B/F/G + D", "pinned per-template shapes (blocker 4), leaf statement [phase, h(B)] (§3.4.1), leaf wrapper build_seg_leaf per template"),
    ("aggregation-M8", "D", "heterogeneous tree over T1's leaves (exists for D0a base templates only; T1 is not D0a)"),
    ("wrap-M9", "D", "ZK wrap over that root with V_d over S only (exists for D0a trees); WrapInitSound / WrapFinalSound"),
    ("lean-e2e", "E", "e2e_sound_t1 premises discharged per lane (SegSound*, NvFaithfulE2E); M11 non-vacuity on T1 done"),
]


def write_report(out, rep):
    wjson(os.path.join(out, "report.json"), rep)
    L = ["# T1 M10 driver report", "", f"case `{rep['case']}`, {rep['date']}", "",
         "| component | owner | status | detail |", "|---|---|---|---|"]
    for name, owner, st, det in rep["table"]:
        L.append(f"| {name} | {owner} | **{st}** | {det} |")
    L += ["", "## Segment plan (lane E T1 templates)", "", "| # | template | owner | d_out | what |", "|---|---|---|---|---|"]
    for s in json.load(open(os.path.join(out, "plan.json")))["segments"]:
        L.append(f"| {s['index']} | {s['template']} | {s['owner']} | `{s['d_out'][:16]}…` | {s['what']} |")
    L += ["", "## Mismatches", ""] + ([f"* **{m['where']}**: {m['msg']}" for m in rep["mismatches"]] or ["none"])
    L.append("")
    open(os.path.join(out, "report.md"), "w").write("\n".join(L))
    print("\n".join(L))


def cmd_run(a):
    out = os.path.abspath(a.out)
    os.makedirs(out, exist_ok=True)
    case = os.path.abspath(a.case)
    ks = [int(x) for x in str(a.steps).split(",")]
    rep = {"case": case, "date": time.strftime("%Y-%m-%d %H:%M:%S"), "steps": {}, "cut_steps": ks}
    rep["tools"] = {n: (p, sha256f(p) if os.path.exists(p) else None) for n, p in
                    [("LEAN_CHECK", LEAN_CHECK), ("WASMBASE_TOOL", WASMBASE_TOOL), ("WASMBASE_TAPE", WASMBASE_TAPE),
                     ("WB_PROVER", WB_PROVER), ("M5A_TOOL", M5A_TOOL), ("M5A_PROVER", M5A_PROVER)]}
    s, pc, cd = step_extract(case, out)
    rep["steps"]["extract"] = s
    s, full = step_lean(case, out, pc)
    rep["steps"]["lean"] = s
    s, calls = step_calls(case, out)
    rep["steps"]["calls"] = s
    comps = {}
    comps["wasm-call"] = comp_wasm_call(out, calls, a.prove)
    comps["wasm-seg"] = comp_wasm_seg(out, calls, ks, a.prove)
    comps["state"] = comp_state(case, out, full, a.prove)
    rep["components"] = comps
    rep["steps"]["plan"] = step_plan(out, cd, full, calls, comps, ks[0])
    ex, pl = rep["steps"]["extract"], rep["steps"]["plan"]
    T = [("Lean checker (allFeatures) + FinalOut reference", "spec", rep["steps"]["lean"]["status"],
          f"verdict {rep['steps']['lean']['verdict']}, FinalOut {rep['steps']['lean']['finalout_equal']}/{rep['steps']['lean']['finalout_rows']} header fields = run outputs"),
         ("statement S (StmtEnc, §3.4.1)", "E/I", ex["status"],
          f"S {ex['S_len']} B (stmtPre {ex['stmtPre_len']} + 4 + stmtPost {ex['stmtPost_len']}), section B {ex['secB_bytes']} B private, "
          f"claimDigest {cd.hex()[:16]}…; = Lean StmtEval {ex['lean_stmt_equal']}; = kernel t1_S_len/t1_claimDigest {ex['t1_kernel_values_equal']}"),
         ("Wasm calls (Lean tape vs clean-room)", "A", rep["steps"]["calls"]["status"],
          f"{rep['steps']['calls']['n_calls']} call(s); {rep['steps']['calls']['source'][:60]}"),
         ("segment plan (BndRec cuts, Templates.lean)", "I/E", pl["status"],
          f"{pl['n_segments']} segments {' / '.join(pl['templates'])}; digest chain {pl['digest_chain_ok']}; "
          f"{pl['lean_bndrec_records']} records = Lean BndRec.encode/bdigest {pl['lean_bndrec_equal']}; placeholders remain")]
    wc = comps["wasm-call"]
    T.append(("Wasm whole call (wasmBaseM2Air)", "A", wc["status"],
              "; ".join(f"call {c['call']}: check {c.get('check_ok')}, return/logs equal {c.get('return_equal')}/{c.get('logs_equal')}"
                        + (f", proved+verified {c.get('verified')} ({c.get('proof_bytes')} B, prove {c.get('prove_s')} s, verify {c.get('verify_s')} s; "
                           f"CODE root recomputed natively from code {str(c.get('code_hash'))[:8]}…)" if "verified" in c else "")
                        for c in wc["calls"])))
    ws = comps["wasm-seg"]

    def wdet(c):
        x = f"call {c['call']} k={c['k']}: {c['segments']} seg, precheck {c['precheck_ok']}, chained {c['chained']}"
        if c.get("error"):
            x += f", {c['error']}"
        if "lean_checks" in c:
            n = sum(1 for r in c["lean_checks"] if r["equal"])
            x += f"; boundary = Lean run {n}/{sum(1 for r in c['lean_checks'] if r['equal'] is not None)}"
            x += f"; Lean HoldsX∧ChipIf {sum(h['HoldsX_ChipIf'] for h in c['lean_holds'])}/{len(c['lean_holds'])}"
        if c.get("proofs"):
            x += "; segprove " + ", ".join(f"{p['proof_bytes']} B {p['prove_s']} s / {p['verify_ms']} ms" for p in c["proofs"])
        return x
    T.append(("Wasm segments (wasmBaseSegAirMP)", "A", ws["status"], "; ".join(wdet(c) for c in ws["calls"])))
    st = comps["state"]
    T.append(("state M5b (INTAKE trie + working set + writes + FINAL root)", "B", st["status"],
              f"post root = header {st.get('post_root_equal_header')}, precheck {st.get('precheck_ok')}"
              + (f", boundary checks {sum(r['equal'] for r in st['boundary_checks'])}/{len(st['boundary_checks'])}" if "boundary_checks" in st else "")
              + (f", verified {st.get('verified')} {st.get('proof_bytes')} B {st.get('prove_s')} s" if "verified" in st else "")
              + (f", {st.get('step')}: {st.get('tail', '')[-120:]}" if st.get("step") else "")))
    for name, owner, what in MISSING:
        T.append((name, owner, "missing", what))
    rep["table"] = T
    rep["mismatches"] = MISMATCHES
    write_report(out, rep)
    if MISMATCHES:
        print(f"FAIL: {len(MISMATCHES)} mismatch(es) between component boundaries and the Lean run", file=sys.stderr)
        return 1
    return 0


# ---------------------------------------------------------------------------
# mutants
# ---------------------------------------------------------------------------
def cmd_mutants(a):
    out = os.path.abspath(a.out)
    md = os.path.join(out, "mutants")
    os.makedirs(md, exist_ok=True)
    claim = open(os.path.join(a.case, "claim.bin"), "rb").read()
    witness = open(os.path.join(a.case, "witness.bin"), "rb").read()
    pc, ms = stmt.mutants(claim)
    # every chunk_inner mutant twice: with the original witness (the witness's own copy of the
    # header then differs: `w.innerBytes == c.chunkInner`), and witness-consistent ("+w": the
    # witness's copy patched too), so the rejection must come from the relation's own checks
    # (headerOk against the computed outputs, section-B authentication, ...)
    ms = [(n, sec, mc, witness) for n, sec, mc in ms] + \
        [(n + "+w", sec, mc, stmt.patch_witness_inner(witness, claim, mc)) for n, sec, mc in ms if sec == "A.inner"]
    b0, b1 = pc["secB"]
    secB = claim[b0:b1]
    s0 = stmt.statement_bytes(claim, pc)
    rows, dirs, seen = [], [], {hashlib.sha256(s0).hexdigest(): "original"}
    for i, (name, sec, mc, wit) in enumerate(ms):
        mpc = None
        try:
            mpc = stmt.parse_claim(mc)
        except Exception as e:  # noqa: BLE001  a mutant that no longer decodes is still a mutant of S
            dec = f"undecodable: {e}"
        else:
            dec = "decodes"
        # section B sits right after chunk_inner: its offset moves only with the inner's length
        b0m = mpc["secB"][0] if mpc else b0 + (len(mc) - len(claim) if name.startswith("inner.") else 0)
        assert mc[b0m:b0m + len(secB)] == secB, f"{name}: section B changed"
        s = mc[:b0m] + stmt.EMPTY_B + mc[b0m + len(secB):]  # S: block vector -> u32 0
        h = hashlib.sha256(s).hexdigest()
        # a "+w" variant is the same statement as its base (only the private witness differs)
        dup = None if name.endswith("+w") else seen.get(h)
        if not name.endswith("+w"):
            seen.setdefault(h, name)
        reb = stmt.splice_secB(s, secB, b0m)
        assert reb == mc, f"{name}: S + section B does not re-assemble the claim"
        dd = os.path.join(md, f"{i:03d}")
        os.makedirs(dd, exist_ok=True)
        open(os.path.join(dd, "claim.bin"), "wb").write(mc)
        open(os.path.join(dd, "witness.bin"), "wb").write(wit)
        dirs.append(dd)
        rows.append({"id": i, "name": name, "section": sec, "decode": dec, "S_sha256": h,
                     "witness": "patched" if wit is not witness else "original",
                     "claimDigest": stmt.claim_digest(s).hex(), "duplicate_of": dup})
    # the Lean checker on every mutant (one process per shard of cases)
    n = max(1, a.jobs)
    shards = [dirs[j::n] for j in range(n)]
    procs = [subprocess.Popen([LEAN_CHECK, "--tier", "allFeatures"] + sh_, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT) for sh_ in shards if sh_]
    verdicts = {}
    for p in procs:
        txt, _ = p.communicate()
        for ln in txt.decode(errors="replace").splitlines():
            try:
                d = json.loads(ln)
            except ValueError:
                continue
            verdicts[os.path.abspath(d["case"])] = (d["verdict"], d["reason"])
    for r, dd in zip(rows, dirs):
        v = verdicts.get(os.path.abspath(dd), ("missing-output", ""))
        r["verdict"], r["reason"] = v
    # every decodable mutant statement evaluated in Lean (StmtEnc), byte for byte
    ev = [(r, os.path.join(dd, "claim.bin")) for r, dd in zip(rows, dirs)
          if r["decode"] == "decodes" and not r["name"].endswith("+w")]
    lrows = stmt.lean_stmt([p for _, p in ev]) or {}
    lean_eq = 0
    for r, p in ev:
        lr = lrows.get(p)
        r["lean_stmt_equal"] = bool(lr and "error" not in lr and lr["claimDigest"] == r["claimDigest"]
                                    and hashlib.sha256(bytes.fromhex(lr["S"])).hexdigest() == r["S_sha256"])
        lean_eq += r["lean_stmt_equal"]
    # one statement per base mutant; its variants (original witness, "+w") share S
    stmts = {}
    for r in rows:
        stmts.setdefault(r["S_sha256"], []).append(r)
    base = [r for r in rows if not r["name"].endswith("+w")]
    distinct = len(stmts) == len(base) and all(r["duplicate_of"] is None for r in base) \
        and hashlib.sha256(s0).hexdigest() not in stmts
    false_s, true_s = [], []
    for h, vs in stmts.items():
        nm = vs[0]["name"]
        # FALSE on T1's (secB, w) family: no variant accepted. A variant the checker accepts makes
        # the mutated statement TRUE (same secB, witness): not a soundness negative, only a
        # binding negative (the T1 proof must not verify against it, since D_wrap binds S).
        acc = [v for v in vs if v["verdict"] == "accept"]
        (true_s if acc else false_s).append(nm)
        for v in vs:
            v["class"] = "true-statement" if acc else "false-statement"
    rej_reasons = {}
    for r in rows:
        if r["verdict"] != "accept":
            rej_reasons.setdefault(r["reason"].split(" (")[0], []).append(r["name"])
    summ = {"case": os.path.abspath(a.case), "checker_sha256": sha256f(LEAN_CHECK),
            "n_runs": len(rows), "n_statements": len(stmts), "distinct_statements": distinct,
            "false_statements": len(false_s), "true_statements": len(true_s),
            "true_statement_fields": true_s,
            "true_statements_explained": "plan §3.4.2 (lane E M11h: each accepted field is unread by the "
                                         "relation, as in nearcore, or read only on paths T1 does not take)",
            "lean_stmt_evaluated": len(ev), "lean_stmt_equal": lean_eq,
            "by_section": {s: sum(1 for r in base if r["section"] == s) for s in ("A", "A.inner", "C")},
            "reject_reasons": {k: len(v) for k, v in sorted(rej_reasons.items())},
            "witness_consistent_inner": {r["name"]: (r["verdict"], r["reason"]) for r in rows if r["name"].endswith("+w")}}
    wjson(os.path.join(out, "mutants.json"), {"summary": summ, "mutants": rows})
    print(json.dumps({k: v for k, v in summ.items() if k != "witness_consistent_inner"}, indent=1))
    for r in rows:
        print(f"{r['id']:03d} {r['verdict']:13s} {r['class']:15s} {r['name']:58s} {r['reason'][:70]}")
    return 0 if distinct and len(false_s) >= 50 and lean_eq == len(ev) else 1


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    r = sp.add_parser("run")
    r.add_argument("case")
    r.add_argument("out")
    r.add_argument("--steps", default="13", help="Wasm steps per segment; a comma list also segchecks the other cut sizes (the plan uses the first)")
    r.add_argument("--prove", action="store_true")
    m = sp.add_parser("mutants")
    m.add_argument("case")
    m.add_argument("out")
    m.add_argument("--jobs", type=int, default=8)
    a = ap.parse_args()
    if a.cmd == "run":
        sys.exit(cmd_run(a))
    else:
        sys.exit(cmd_mutants(a))


if __name__ == "__main__":
    main()
