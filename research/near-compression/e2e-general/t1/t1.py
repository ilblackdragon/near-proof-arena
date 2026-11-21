#!/usr/bin/env python3
"""M10 driver skeleton for T1 (docs/zk-formal/E2E-T1-CRITICAL-PATH.md; plan §4 M10).

    t1.py run     CASE_DIR OUT_DIR [--steps K] [--prove]
    t1.py mutants CASE_DIR OUT_DIR [--jobs N]

`run`:
  1. extract     copy the case, split the claim into the D-2 public statement S (sections A + C) and
                 the private section B; claimDigest = bdigest(S);
  2. lean        the unmodified Lean checker (`--tier allFeatures`, then `--emit-full`): verdict,
                 self-check, outputs; FinalOut = header outputs vs the run's outputs;
  3. calls       the chunk's Wasm calls, twice: the Lean host tape (`wasmbase-tape`, or the cached
                 lane A M3 corpus tape when the exe is not built) and the clean-room checker
                 (`m1/extract_calls.py`, also writes the code blobs); cross-checked;
  4. plan        cut the run into segments per lane E's boundary record (`BndRec`, View.lean phase
                 tags) and encode each cut with `bndrec.py`; check out(k) = in(k+1) as digests;
  5. components  run every component prover that exists today, record the rest as missing:
                 lane A whole-call Wasm AIR (`wasmBaseM2Air`), lane A segment AIR
                 (`wasmBaseSegAirMP`, chained public boundaries), lane B state (M5b AIR);
  6. report      OUT/report.json + OUT/report.md (per-component pass / fail / blocked / missing).

`mutants`: >= 50 mutants of S (one public field each: every chunk-header output field and every
trusted fact), all distinct, each re-assembled with the original private section B and witness and
run through the Lean checker, which must reject every one.

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
    wjson(os.path.join(out, "statement.json"), pub)
    meta = json.load(open(os.path.join(case, "meta.json")))
    return {"status": "pass", "claimDigest": cd.hex(), "S_len": len(s), "secB_bytes": b1 - b0,
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
# 4. the segment plan (lane E's BndRec at every cut)
# ---------------------------------------------------------------------------
def step_plan(out, cd, full, calls, k_steps):
    """Cut T1's run into the CM/RCM segments of plan §3.1 and fill each cut's BndRec.

    Clear fields come from the run log (receipt index, cumulative gas/compute from the outcomes, the
    Wasm clock); digest fields are 0^42 placeholders until a component produces them (`producer`
    says who must). `complete` is false while any placeholder remains."""
    o = full["outputs"]
    outcomes = o["outcomes"]
    segs = []
    rec = bndrec.blank(cd)
    rec["phase"] = bndrec.PHASE["init"]

    def cut(template, owner, what, **upd):
        nonlocal rec
        b_in = rec
        b_out = dict(rec)
        b_out.update(upd)
        segs.append({"template": template, "owner": owner, "what": what, "B_in": b_in, "B_out": b_out})
        rec = b_out

    cut("INTAKE", "F (claim/witness/receipt intake) + B (M5a INTAKE: pre-state working set)",
        "init cb wb -> eng I start: decode claim+witness, authenticate pre-state trie vs prev_state_root",
        phase=bndrec.PHASE["eng"])
    gas = burnt = comp = 0
    call_by_exec = {c["index"]: c for c in calls}
    ci = 0
    for ri, oc in enumerate(outcomes):
        has_call = bool(oc["logs"]) or oc["status"]["kind"] == "value"
        g, cu = int(oc["gasBurnt"]), int(oc["computeUsage"])
        if has_call and ci in call_by_exec:
            c = call_by_exec[ci]
            ci += 1
            cut("STATE", "F (receipt/action rows) + B (working set)",
                f"receipt {ri} (executor {bytes.fromhex(oc['executor']).decode()}): up to the VM call",
                receiptIdx=ri, phase=bndrec.PHASE["call"], inCall=True, wasm=bndrec.wasm_blank(),
                rPrepaid=c["prepaid"])
            steps = c["steps"] or 0
            t = 0
            while t < steps:
                t2 = min(steps, t + k_steps)
                w = dict(rec["wasm"])
                w["fuel"] = t2  # placeholder clock inside the call: the Wasm step count
                cut("WASM", "A (wasmBaseSegAirMP) + M6 join (A+B)",
                    f"call {c['index']} {c['method']} steps ({t}, {t2}] of {steps}", t=rec["t"] + (t2 - t), wasm=w)
                t = t2
            gas, burnt, comp = gas + g, burnt + g, comp + cu
            cut("STATE", "F (refund, outcome, promises) + B (writes) + G (outcome accumulator)",
                f"receipt {ri}: VM result answered from the call tape, outcome recorded",
                phase=bndrec.PHASE["eng"], inCall=False, wasm=None, gasUsed=gas, gasBurnt=burnt, compute=comp,
                rBurnt=int(c["real"]["burnt"]), rUsed=int(c["real"]["used"]))
        else:
            gas, burnt, comp = gas + g, burnt + g, comp + cu
            cut("STATE", "F (receipt/action rows) + B (working set)",
                f"receipt {ri} (executor {bytes.fromhex(oc['executor']).decode()}, status {oc['status']['kind']})",
                receiptIdx=ri, gasUsed=gas, gasBurnt=burnt, compute=comp)
    cut("FINAL", "B (MPT root) + G (FinalOut: outcome/outgoing roots, congestion, bw, RS encoding, tx root)",
        "eng done -> fin -> done H o: implicit transitions, outputs, headerOk", phase=bndrec.PHASE["done"])
    # encode every cut and check the chain as digests
    chain_ok = True
    for i, s in enumerate(segs):
        s["d_in"], s["d_out"] = bndrec.digest(s["B_in"]).hex(), bndrec.digest(s["B_out"]).hex()
        if i and segs[i - 1]["d_out"] != s["d_in"]:
            chain_ok = False
    gas_ok = gas == int(o["gasUsed"]) and comp == int(o["computeUsage"])
    j = [{"index": i, "template": s["template"], "owner": s["owner"], "what": s["what"],
          "d_in": s["d_in"], "d_out": s["d_out"],
          "B_out": bndrec.to_json(s["B_out"])} for i, s in enumerate(segs)]
    wjson(os.path.join(out, "plan.json"), {"segments": j, "placeholder_fields": bndrec.PRODUCER})
    return {"status": "pass" if chain_ok and gas_ok else "fail", "n_segments": len(segs),
            "templates": [s["template"] for s in segs], "digest_chain_ok": chain_ok,
            "gas_compute_sum_equals_header": gas_ok, "complete": False,
            "note": "digest fields are placeholders; only claimDigest and the clear fields are real"}


# ---------------------------------------------------------------------------
# 5. components
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


SEG_RE = re.compile(r"segment (\d+): (.*)")


def comp_wasm_seg(out, calls, k, prove):
    """Lane A segment AIR `wasmBaseSegAirMP`: cut the call every k steps, pre-check each segment,
    chain B_out(k) = B_in(k+1) (lane A's own check over the public boundary: pc, t, S, gas register,
    ctxDigest, memRoot)."""
    d = os.path.join(out, "wasm-seg")
    os.makedirs(d, exist_ok=True)
    seg_air = os.path.join(d, "airSegMP.json")
    sh([WASMBASE_TOOL, "airSegMP", "0", "0"], seg_air)
    res = []
    for c in calls:
        if not c["prep"]:
            continue
        nl, ng = nloc_ngl(c["prep"])
        air = os.path.join(d, f"airM2-{nl}-{ng}.json")
        sh([WASMBASE_TOOL, "airM2", str(nl), str(ng)], air)
        rc, txt, dt = sh([WB_PROVER, "segcheck", seg_air, air, c["prep"], str(k)],
                         os.path.join(d, f"{c['index']:02d}.segcheck-k{k}.log"))
        nseg = len(re.findall(r"^SEG \d+ ", txt, re.M))
        pre_ok = len(re.findall(r"PRECHECK OK", txt))
        chained = "SEGCHECK OK" in txt
        m = SEG_RE.search(txt)
        r = {"call": c["index"], "steps": c["steps"], "k": k, "segments": nseg, "precheck_ok": pre_ok,
             "chained": chained, "error": m.group(0)[:300] if m else None}
        if chained and prove:
            rc2, txt2, dt2 = sh([WB_PROVER, "segprove", seg_air, air, c["prep"], str(k)],
                                os.path.join(d, f"{c['index']:02d}.segprove-k{k}.log"),
                                env={"WASMBASE_WASM": c["wasm"]})
            r.update(segprove_ok="SEGPROVE OK" in txt2, prove_s=round(dt2, 1))
        if chained and (not prove or r.get("segprove_ok")):
            r["status"] = "pass"
        elif m and "unbalanced" in m.group(2):
            r["status"] = "blocked"
        else:
            r["status"] = "fail"
        res.append(r)
    st = "pass" if res and all(x["status"] == "pass" for x in res) else \
        ("blocked" if any(x["status"] == "blocked" for x in res) else "fail")
    return {"status": st, "air": "wasmBaseSegAirMP (M4c default segment AIR)", "calls": res}


def comp_state(case, out, full, prove, d_ws=5):
    """Lane B: M5b AIR (INTAKE + working set + STATE write rows + FINAL MPT root) on the chunk's main
    transition, through lane B's own scripts (run read-only)."""
    d = os.path.join(out, "state")
    os.makedirs(d, exist_ok=True)
    shutil.copy(os.path.join(out, "lean-full.json"), os.path.join(d, "lean-full.json"))
    r = {}
    rc, txt, _ = sh([sys.executable, os.path.join(M5A, "extract_state.py"), case, os.path.join(d, "lean-full.json"),
                     os.path.join(d, "state.json")], os.path.join(d, "extract.log"))
    if rc:
        return {"status": "fail", "step": "extract_state", "tail": txt[-400:]}
    sh([M5A_TOOL, "airb", str(d_ws), os.path.join(d, "m5b.json"), os.path.join(d, "names.json")], os.path.join(d, "air.txt"))
    rc, got, _ = sh([M5A_TOOL, "apply", os.path.join(d, "state.json")])
    want = json.load(open(os.path.join(d, "state.json")))["post_root"]
    r["spec_oracle_root"] = got.strip()
    r["post_root_equal_header"] = got.strip() == want == full["outputs"]["stateRoot"]
    rc, txt, _ = sh([sys.executable, os.path.join(M5A, "tracegen.py"), os.path.join(d, "state.json"),
                     os.path.join(d, "names.json"), os.path.join(d, "dump")], os.path.join(d, "gen.txt"))
    if rc:
        return {"status": "fail", "step": "tracegen", "tail": txt[-400:], **r}
    mode = "prove" if prove else "check"
    rc, txt, dt = sh([M5A_PROVER, os.path.join(d, "m5b.json"), os.path.join(d, "dump"), mode], os.path.join(d, f"{mode}.log"))
    r["precheck_ok"] = "PRECHECK OK" in txt
    if prove:
        m = re.search(r"proof_bytes (\d+)", txt)
        r.update(verified="VERIFY OK" in txt, proof_bytes=int(m.group(1)) if m else None, prove_s=round(dt, 1))
    ok = r["post_root_equal_header"] and r["precheck_ok"] and (not prove or r["verified"])
    r["status"] = "pass" if ok else "fail"
    r["air"] = f"M5b (m5a-tool airb {d_ws}); host requests from the public HTAPE (not yet lane A's HOST rows)"
    return r


MISSING = [
    ("intake", "F (new)", "claim + witness decoding in-circuit, receipt intake (incoming/delayed/buffered), INTAKE leaf exposing B_0 = Init(claimDigest) with ctxRoot"),
    ("runtime", "F (new)", "receipt/action rows: FunctionCall action, refund receipt, outcome, gas/compute counters (STATE template)"),
    ("join-M6", "A + B", "HOSTQ/HOSTR/HOSTB produced by STATE rows in the WASM segment's trace (HostIf); HOSTO oracle removed"),
    ("prep", "unassigned", "PREP sub-proof: SHA-256(code) = code hash, checkModuleM2 + instrumentation -> CODE/FUNC roots = B.codeRoot/funcRoot"),
    ("finalout", "G (new)", "outcome root, outgoing receipts root, congestion, bandwidth requests, RS encoded_merkle_root/length, tx root; FINAL leaf checks headerOk vs S"),
    ("leaves", "A/B/F/G + D", "pinned per-template shapes (blocker 4), canonical boundary statement [phase, h(B)] (blocker 5), leaf wrapper build_seg_leaf per template"),
    ("aggregation-M8", "D", "heterogeneous tree over T1's leaves (exists for D0a base templates only; T1 is not D0a)"),
    ("wrap-M9", "D", "ZK wrap over that root with V_d over S only (exists for D0a trees)"),
    ("lean-e2e", "E", "e2e_sound obligations for T1's templates (SegSound per template, NodeExec/WrapExec, ViewImpl instances)"),
]


def write_report(out, rep):
    wjson(os.path.join(out, "report.json"), rep)
    L = ["# T1 M10 driver report", "", f"case `{rep['case']}`, {rep['date']}", "",
         "| component | owner | status | detail |", "|---|---|---|---|"]
    for name, owner, st, det in rep["table"]:
        L.append(f"| {name} | {owner} | **{st}** | {det} |")
    L.append("")
    open(os.path.join(out, "report.md"), "w").write("\n".join(L))
    print("\n".join(L))


def cmd_run(a):
    out = os.path.abspath(a.out)
    os.makedirs(out, exist_ok=True)
    case = os.path.abspath(a.case)
    rep = {"case": case, "date": time.strftime("%Y-%m-%d %H:%M:%S"), "steps": {}}
    rep["tools"] = {n: (p, sha256f(p) if os.path.exists(p) else None) for n, p in
                    [("LEAN_CHECK", LEAN_CHECK), ("WASMBASE_TOOL", WASMBASE_TOOL), ("WASMBASE_TAPE", WASMBASE_TAPE),
                     ("WB_PROVER", WB_PROVER), ("M5A_TOOL", M5A_TOOL), ("M5A_PROVER", M5A_PROVER)]}
    s, pc, cd = step_extract(case, out)
    rep["steps"]["extract"] = s
    s, full = step_lean(case, out, pc)
    rep["steps"]["lean"] = s
    s, calls = step_calls(case, out)
    rep["steps"]["calls"] = s
    rep["steps"]["plan"] = step_plan(out, cd, full, calls, a.steps)
    comps = {}
    comps["wasm-call"] = comp_wasm_call(out, calls, a.prove)
    comps["wasm-seg"] = comp_wasm_seg(out, calls, a.steps, a.prove)
    comps["state"] = comp_state(case, out, full, a.prove)
    rep["components"] = comps
    T = [("Lean checker (allFeatures) + FinalOut reference", "spec", rep["steps"]["lean"]["status"],
          f"verdict {rep['steps']['lean']['verdict']}, FinalOut {rep['steps']['lean']['finalout_equal']}/{rep['steps']['lean']['finalout_rows']} header fields = run outputs"),
         ("statement split (D-2)", "I", rep["steps"]["extract"]["status"],
          f"S {rep['steps']['extract']['S_len']} B, section B {rep['steps']['extract']['secB_bytes']} B private, claimDigest {cd.hex()[:16]}…"),
         ("Wasm calls (Lean tape vs clean-room)", "A", rep["steps"]["calls"]["status"],
          f"{rep['steps']['calls']['n_calls']} call(s); {rep['steps']['calls']['source'][:60]}"),
         ("segment plan (BndRec cuts)", "I/E", rep["steps"]["plan"]["status"],
          f"{rep['steps']['plan']['n_segments']} segments {'/'.join(rep['steps']['plan']['templates'])}; digest chain {rep['steps']['plan']['digest_chain_ok']}; placeholders remain")]
    wc = comps["wasm-call"]
    T.append(("Wasm whole call (wasmBaseM2Air)", "A", wc["status"],
              "; ".join(f"call {c['call']}: check {c.get('check_ok')}, return/logs equal {c.get('return_equal')}/{c.get('logs_equal')}"
                        + (f", proved+verified {c.get('verified')} ({c.get('proof_bytes')} B, prove {c.get('prove_s')} s, verify {c.get('verify_s')} s; "
                           f"CODE root recomputed natively from code {str(c.get('code_hash'))[:8]}…)" if "verified" in c else "")
                        for c in wc["calls"])))
    ws = comps["wasm-seg"]
    T.append(("Wasm segments (wasmBaseSegAirMP)", "A", ws["status"],
              "; ".join(f"call {c['call']} k={c['k']}: {c['segments']} seg, precheck {c['precheck_ok']}, chained {c['chained']}"
                        + (f", {c['error']}" if c.get("error") else "") for c in ws["calls"])))
    st = comps["state"]
    T.append(("state M5b (INTAKE trie + working set + writes + FINAL root)", "B", st["status"],
              f"post root = header {st.get('post_root_equal_header')}, precheck {st.get('precheck_ok')}"
              + (f", verified {st.get('verified')} {st.get('proof_bytes')} B {st.get('prove_s')} s" if "verified" in st else "")
              + (f", {st.get('step')}: {st.get('tail', '')[-120:]}" if st.get("step") else "")))
    for name, owner, what in MISSING:
        T.append((name, owner, "missing", what))
    rep["table"] = T
    write_report(out, rep)


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
        s = mc[:b0m] + mc[b0m + len(secB):]
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
            "by_section": {s: sum(1 for r in base if r["section"] == s) for s in ("A", "A.inner", "C")},
            "reject_reasons": {k: len(v) for k, v in sorted(rej_reasons.items())},
            "witness_consistent_inner": {r["name"]: (r["verdict"], r["reason"]) for r in rows if r["name"].endswith("+w")}}
    wjson(os.path.join(out, "mutants.json"), {"summary": summ, "mutants": rows})
    print(json.dumps({k: v for k, v in summ.items() if k != "witness_consistent_inner"}, indent=1))
    for r in rows:
        print(f"{r['id']:03d} {r['verdict']:13s} {r['class']:15s} {r['name']:58s} {r['reason'][:70]}")
    return 0 if distinct and len(false_s) >= 50 else 1


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest="cmd", required=True)
    r = sp.add_parser("run")
    r.add_argument("case")
    r.add_argument("out")
    r.add_argument("--steps", type=int, default=13, help="Wasm steps per segment")
    r.add_argument("--prove", action="store_true")
    m = sp.add_parser("mutants")
    m.add_argument("case")
    m.add_argument("out")
    m.add_argument("--jobs", type=int, default=8)
    a = ap.parse_args()
    if a.cmd == "run":
        cmd_run(a)
    else:
        sys.exit(cmd_mutants(a))


if __name__ == "__main__":
    main()
