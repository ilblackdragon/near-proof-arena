#!/usr/bin/env python3
"""Three-way differential test for near/pv86/receipt-transfer-batch/v0.

  1. near-arena-oracle  (real pinned nearcore Runtime::apply)  -> claim.bin / out-of-domain verdict
  2. nearspec-check     (compiled Lean reference semantics)    -> claim bytes / out_of_domain
  3. spec_check.py      (independent Python, full-trie rebuild) -> claim bytes / out_of_domain

Every case must satisfy: all three agree on in-domain-ness, and for in-domain
cases all three produce byte-identical claims (and Lean's decide(NearRelation)
holds). Usage:

  difftest.py --seed S --valid N --invalid M [--workdir DIR] [--report FILE]
"""
import argparse, collections, json, os, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check as sc

def coverage(d, cov):
    """Count domain features exercised by an in-domain case (from request/state only)."""
    req = sc.parse_request(open(os.path.join(d, "request.bin"), "rb").read())
    kv = sc.parse_state(open(os.path.join(d, "state.bin"), "rb").read())
    rs = req["receipts"]
    recvs = [x["recv"] for x in rs]
    keys = sorted(k for k in kv if k[:1] == b"\0")
    if len(set(recvs)) < len(recvs): cov["repeated_receiver"] += 1
    if any(any(k != b"\0" + r and k.startswith(b"\0" + r) for k in keys) for r in recvs):
        cov["receiver_key_is_prefix_of_another_key(branch_with_value)"] += 1
    if any(len(r) == 64 for r in recvs): cov["receiver_len_64"] += 1
    if any(len(r) == 2 for r in recvs): cov["receiver_len_2"] += 1
    if any(x["dep"] == 0 for x in rs): cov["deposit_zero"] += 1
    if (len(rs) - 1) * sc.G + 1 == req["gas_limit"]: cov["gas_limit_tight"] += 1
    if any(x["gp"] < req["bgp"] for x in rs): cov["receipt_price_below_block_price"] += 1
    if any(x["gp"] == 0 for x in rs): cov["receipt_price_zero"] += 1
    if any(x["pk"][0] == 1 for x in rs): cov["secp256k1_signer_key"] += 1
    cur = dict(kv); hit_max = False
    for x in rs:
        k = b"\0" + x["recv"]; v = cur[k]
        na = int.from_bytes(v[:16], "little") + x["dep"]; lk = int.from_bytes(v[16:32], "little")
        if na > sc.U128_MAX - 2**64 or na + lk > sc.U128_MAX - 2**64: hit_max = True
        cur[k] = sc.u128(na) + v[16:]
    if hit_max: cov["balance_within_2^64_of_u128_max"] += 1
    if len(rs) >= 128: cov["batch_ge_128"] += 1

HERE = os.path.dirname(os.path.abspath(__file__))
ORACLE_DIR = os.path.dirname(HERE)
REPO = os.path.dirname(ORACLE_DIR)
ORACLE = os.path.join(ORACLE_DIR, "target/debug/near-arena-oracle")
LEAN = os.path.join(REPO, "spec/lean/.lake/build/bin/nearspec-check")
PY = os.path.join(HERE, "spec_check.py")

def run_lines(cmd):
    t = time.time()
    p = subprocess.run(cmd, capture_output=True, text=True)
    lines = [json.loads(l) for l in p.stdout.splitlines() if l.strip()]
    return lines, p.returncode, p.stderr.strip().splitlines()[-1:] , time.time() - t

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=1000)
    ap.add_argument("--valid", type=int, default=500)
    ap.add_argument("--invalid", type=int, default=70)
    ap.add_argument("--workdir")
    ap.add_argument("--report")
    a = ap.parse_args()
    work = a.workdir or tempfile.mkdtemp(prefix="difftest-")
    cases_dir = os.path.join(work, f"seed{a.seed}")
    subprocess.run(["rm", "-rf", cases_dir], check=True)
    t0 = time.time()
    g = subprocess.run([ORACLE, "gen", "--seed", str(a.seed), "--valid", str(a.valid),
                        "--invalid", str(a.invalid), "--with-example", "--out", cases_dir],
                       capture_output=True, text=True)
    t_gen = time.time() - t0
    lean, lrc, lsum, t_lean = run_lines([LEAN, cases_dir])
    py, prc, psum, t_py = run_lines([sys.executable, PY, cases_dir])
    L = {os.path.basename(x["case"]): x for x in lean}
    P = {os.path.basename(x["case"]): x for x in py}
    names = sorted(os.listdir(cases_dir))
    disagreements = []
    stats = collections.Counter()
    profiles = collections.Counter()
    sizes = []
    cov = collections.Counter()
    for n in names:
        d = os.path.join(cases_dir, n)
        diag = json.load(open(os.path.join(d, "diagnostics.json")))
        oracle_in = diag["in_domain"]
        oracle_claim = open(os.path.join(d, "claim.bin"), "rb").read().hex() if oracle_in else None
        l, p = L.get(n), P.get(n)
        ok = (diag["consistent"] and l is not None and p is not None)
        if ok and oracle_in:
            ok = (l["status"] == "ok" and p["status"] == "ok" and l["claim"] == p["claim"] == oracle_claim)
            stats["in_domain_agree" if ok else "in_domain_DISAGREE"] += 1
            profiles[diag["generator"]["profile"]] += 1
            sizes.append(diag["sizes"]["receipts"])
            coverage(d, cov)
            if diag["claim"]["refund_count"] > 0: stats["with_refunds"] += 1
            else: stats["without_refunds"] += 1
        elif ok:
            ok = l["status"] == "out_of_domain" and p["status"] == "out_of_domain"
            stats["out_of_domain_agree" if ok else "out_of_domain_DISAGREE"] += 1
            profiles["invalid:" + (diag["generator"]["invalid_kind"] or "?")] += 1
        if not ok:
            disagreements.append(dict(case=n, oracle=diag.get("domain_reason"), oracle_consistent=diag["consistent"],
                                      nearcore_problems=diag.get("nearcore_problems"),
                                      lean=l and {k: l[k] for k in ("status", "reason")},
                                      python=p and {k: p[k] for k in ("status", "reason")}))
    report = dict(
        seed=a.seed, cases=len(names), stats=dict(stats), disagreements=disagreements,
        batch_size={"min": min(sizes, default=0), "max": max(sizes, default=0),
                    "mean": round(sum(sizes) / max(len(sizes), 1), 1)},
        profiles=dict(sorted(profiles.items())),
        coverage=dict(sorted(cov.items())),
        timings_s={"oracle_gen": round(t_gen, 2), "lean_check": round(t_lean, 2), "python_check": round(t_py, 2)},
        tool_summaries={"oracle": g.stderr.strip().splitlines()[-1:], "lean": lsum, "python": psum},
        exit_codes={"oracle": g.returncode, "lean": lrc, "python": prc},
    )
    s = json.dumps(report, indent=1)
    print(s)
    if a.report:
        open(a.report, "w").write(s + "\n")
    sys.exit(0 if not disagreements and g.returncode == 0 and lrc == 0 and prc == 0 else 1)

if __name__ == "__main__":
    main()
