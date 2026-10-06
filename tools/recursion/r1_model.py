#!/usr/bin/env python3
"""R1 cost model for np-udr-stark-v1 ("one STARK, many segment tables, global buses").

docs/research/recursion-r1-cost.md is the write-up; every constant below is cited there.

  python3 r1_model.py check      # analytic size model vs the exact/measured calibration points
  python3 r1_model.py curves     # S-curves, 8 MiB / 64 MiB crossings, cost-board break-even
  python3 r1_model.py fit        # least-squares fits of the measured verify/prove data

Proof bytes are an *analytic expectation* over uniformly random query positions (the
positions come from the transcript); `r1calib breakdown` gives the exact bytes of a real
proof and `r1calib expect` a Monte-Carlo mean, both from the prover's own schedule code.
"""
import math
import sys

# ---- protocol constants (examples/np-udr-stark-fast2/source/src/protocol.rs; FORMATS.md) ----
Q = 24 * 9          # NUM_CHUNKS * PER_CHUNK = 216 query positions (duplicates kept)
LOG_BLOWUP = 4      # rate 1/16
MAX_ARITY_LOG = 3   # FRI commitments of arity <= 8
DIG = 64            # WH digest bytes (Merkle node / root)
FB = 4              # base-field element (u32 le)
KB = 32             # extension element (8 limbs)
CAP_8MIB = 8 << 20
CAP_64MIB = 64 << 20

# ---- arena price model pm-near-mainnet-2026q4 (draft; BENCHMARK_SPEC §14.7) ----
N_V = 84
V_P = 8
V_V = 8
C_CPU = 7.61e9      # fUSD per vCPU-second
C_BW = 82_000       # fUSD per byte per validator
C_STORE = 0


def p_hit(n, q=Q):
    """P(a fixed one of n equiprobable slots is hit by >= 1 of q uniform draws)."""
    return 1.0 - (1.0 - 1.0 / n) ** q


def tree_bytes(depth, rows_at_level):
    """Expected multiproof bytes of one MMCS tree of `depth` (2^depth leaves) opened at Q
    uniform layer-0 positions. rows_at_level[k] = bytes of the rows injected at level k
    (k = 0 leaves). Returns (row bytes, sibling bytes, E[#siblings])."""
    rows = sib = 0.0
    for k in range(depth + 1):
        nk = 2 ** (depth - k)
        uk = nk * p_hit(nk)
        rows += uk * rows_at_level.get(k, 0)
        if k >= 1:
            nc = 2 * nk  # children level size
            p1 = (1 - 1 / nc) ** Q
            p2 = (1 - 2 / nc) ** Q
            sib += nk * 2 * (p1 - p2)
    return rows, DIG * sib, sib


def schedule(heights):
    """FRI schedule of protocol.rs Schedule::new: (l0, fri_l, committed[(c, a)])."""
    hmax = max(heights)
    l0 = hmax + LOG_BLOWUP
    classes = sorted(set(hmax - h for h in heights))
    fri_l = hmax - 1
    committed, k = [], 0
    while fri_l > 0:
        nxt_class = min([c for c in classes if c > k], default=10 ** 9)
        nxt = min(k + MAX_ARITY_LOG, nxt_class, fri_l)
        committed.append((k, nxt - k))
        if nxt == fri_l:
            break
        k = nxt
    return l0, fri_l, committed


def proof_bytes(tables, detail=False):
    """tables: list of dicts h (log height), w (base cols), a (aux K cols), q (quotient
    K chunks), f (bus finals). Expected proof bytes (FORMATS.md §5)."""
    hs = [t["h"] for t in tables]
    l0, fri_l, committed = schedule(hs)
    nt = len(tables)
    fixed = 8 + nt + 3 * DIG + 64              # header, 3 roots, final poly
    finals = KB * sum(t["f"] for t in tables)
    ood = KB * sum(2 * t["w"] + 2 * t["a"] + t["q"] for t in tables)
    fri_roots = DIG * len(committed)
    out = {"fixed": fixed, "finals": finals, "ood": ood, "fri_roots": fri_roots}
    for name, unit in (("main", lambda t: FB * t["w"]), ("aux", lambda t: KB * t["a"]),
                       ("quot", lambda t: KB * t["q"])):
        lvl = {}
        for t in tables:
            k = l0 - (t["h"] + LOG_BLOWUP)
            lvl[k] = lvl.get(k, 0) + unit(t)
        r, s, _ = tree_bytes(l0, lvl)
        out[name + "_rows"], out[name + "_sib"] = r, s
    fr = fs = 0.0
    for (c, a) in committed:
        r, s, _ = tree_bytes(l0 - c - a, {0: KB * (2 ** a)})
        fr += r
        fs += s
    out["fri_rows"], out["fri_sib"] = fr, fs
    out["total"] = sum(v for v in out.values())
    return out if detail else out["total"]


# ---- tables -------------------------------------------------------------------------------
def T(h, w, a, q=3, f=None):
    return {"h": h, "w": w, "a": a, "q": q, "f": a if f is None else f}


NEAR_MAX = [T(22, 544, 17), T(22, 163, 13), T(16, 12, 4), T(17, 228, 13), T(12, 16, 13),
            T(14, 58, 5), T(13, 49, 1)]   # r1calib shape near-air.json + max-case header


def toy_seg_air(S, h, widths, k=8):
    """r1calib `seg` instance: io table (16 rows, 2k cols, 2 interactions) + S x widths;
    table 0 of each segment has the 2 boundary interactions, the others are cube tables."""
    ts = [T(4, 2 * k, 2)]
    for _ in range(S):
        for i, w in enumerate(widths):
            ts.append(T(h, w, 2 if i == 0 else 0))
    return ts


# D3 segment presets (ASSUMPTIONS, docs/research/recursion-r1-cost.md §4.1). Each segment holds
# OPS_PER_SEG WASM operators: EXEC 1 row/op; sorted RAM 3 rows/op split into 3 tables of 2^22
# rows chained by a 2-interaction boundary bus; all multiplicities 1-bit (as in nearAir).
PRESETS = {
    # EXEC 150 cols, 10 interactions (3 RAM, CODE, 4 ALU/range, 2 boundary); RAM 16 cols,
    # 5 interactions (perm receive, 2 range sends, 2 chain).
    "d3-lean": [T(22, 150, 10), T(22, 16, 5), T(22, 16, 5), T(22, 16, 5)],
    # EXEC 300 cols, 16 interactions; RAM 24 cols, 6 interactions; per-segment ALU chip
    # (limb/carry rows, 1 row/op) 60 cols, 6 interactions.
    "d3-rich": [T(22, 300, 16), T(22, 24, 6), T(22, 24, 6), T(22, 24, 6), T(22, 60, 6)],
    # the real nearAir density (t0+t1 of the max case) as a per-segment table set
    "near-density": [T(22, 544, 17), T(22, 163, 13)],
}
# segment-independent global tables (CODE, byte/range providers, io/boundary), once per proof
GLOBAL = [T(20, 24, 4), T(17, 8, 2), T(16, 8, 2), T(4, 32, 2)]
OPS_PER_SEG = 2 ** 22
MSG_LEN_P1 = 13                    # assumed max bus message length + 1
REGULAR_OP_COST = 822_756          # gas per WASM operator (PV86)
GAS_MAX = 10 ** 15                 # chunk gas limit


def r1_air(S, preset):
    return GLOBAL + PRESETS[preset] * S


def weq(tables):
    """base-column equivalents committed (main + 8*aux + 8*quot), height-weighted to 2^22."""
    return sum((t["w"] + 8 * t["a"] + 8 * t["q"]) * 2 ** (t["h"] - 22) for t in tables)


# ---- time / memory models (fitted in `fit`; see the doc §3) ------------------------------
# Prove: seconds per committed base-column equivalent (W_eq = w + 8a + 8q) at height 2^22,
# 8 rayon threads, AVX2, CPUs 8-15 (CCD1) of the shared host:
PROVE_S_PER_WEQ22 = {
    "near-anchor": 381.4 / 995.0,   # gen-max NEAR proof, 381.4 s, W_eq 995 (+7% small tables)
    "toy-anchor": 231.0 / 310.0,    # r1calib seg 1 22 150,16,16,16: 231.0 s, W_eq 310 (+io)
}
# Peak RSS of the *current* (non-streaming) prover at 2^22 (measured, GB)
RSS_GB = {"near-anchor": 9.11, "toy-anchor": 11.3}


def ood_count(tables):
    return sum(2 * t["w"] + 2 * t["a"] + t["q"] for t in tables)


def lean_verify_ms(tables, fit, nbytes=None):
    """fit = (a, b_per_MB, c_per_ood, d_per_ntables*ood/1e3)."""
    a, b, c, d = fit
    B = (proof_bytes(tables) if nbytes is None else nbytes) / 1e6
    ood = ood_count(tables)
    return a + b * B + c * ood + d * len(tables) * ood / 1e3


def cost_fusd(prove_s, verify_s, nbytes):
    """BENCHMARK_SPEC §14.3 total_fusd for one request (ceil()s omitted)."""
    return (C_CPU * V_P * prove_s + N_V * (C_CPU * V_V * verify_s)
            + N_V * nbytes * (C_BW + C_STORE))


# D3 re-execution reference (witness-as-proof): Lean W3 interpreter speed from the PoC
# (near-wasm-strategy.md §5: a 300 Tgas loop in ~10 s) -> 30 Tgas/s; prove ~0.
REEXEC_GAS_PER_S = 30e12


# ---- commands -----------------------------------------------------------------------------
MEASURED_SIZES = [
    # (label, tables, measured bytes) — measured = file sizes of real proofs
    ("NEAR max case (gen-max, 2^22)", NEAR_MAX, 3_561_135),
]


def read_tsv(path):
    rows = []
    with open(path) as fh:
        hdr = fh.readline().rstrip("\n").split("\t")
        for ln in fh:
            v = ln.rstrip("\n").split("\t")
            rows.append(dict(zip(hdr, v)))
    return rows


def cmd_check(resdir):
    print("label\tmodel_B\tmeasured_B\terr%")
    for lab, ts, meas in MEASURED_SIZES:
        m = proof_bytes(ts)
        print(f"{lab}\t{m:.0f}\t{meas}\t{100 * (m - meas) / meas:+.2f}")
    import glob
    import os
    near = [(t["w"], t["a"], t["q"], t["f"]) for t in NEAR_MAX]
    for r in read_tsv(os.path.join(resdir, "near-proofs.tsv")):
        hs = [int(x) for x in r["heights"].split(",")]
        ts = [T(h, w, a, q, f) for h, (w, a, q, f) in zip(hs, near)]
        m, meas = proof_bytes(ts), int(r["proof_B"])
        print(f"NEAR {r['label']} h={r['heights']}\t{m:.0f}\t{meas}\t{100 * (m - meas) / meas:+.2f}")
    for f in sorted(glob.glob(os.path.join(resdir, "*.tsv"))):
        for r in read_tsv(f):
            if not r.get("proof_B") or "S" not in r:
                continue
            S, h = int(r["S"]), int(r["log_h"])
            ws = [int(x) for x in r["widths"].split(",")]
            m = proof_bytes(toy_seg_air(S, h, ws, int(r["k"])))
            meas = int(r["proof_B"])
            print(f"{os.path.basename(f)} S={S} h={h} w={r['widths']}\t{m:.0f}\t{meas}\t{100 * (m - meas) / meas:+.2f}")


def lstsq(X, y):
    # tiny normal-equation solver (no numpy dependency)
    n = len(X[0])
    A = [[sum(X[k][i] * X[k][j] for k in range(len(X))) for j in range(n)] for i in range(n)]
    b = [sum(X[k][i] * y[k] for k in range(len(X))) for i in range(n)]
    for i in range(n):
        p = max(range(i, n), key=lambda r: abs(A[r][i]))
        A[i], A[p], b[i], b[p] = A[p], A[i], b[p], b[i]
        for r in range(n):
            if r != i:
                f = A[r][i] / A[i][i]
                A[r] = [A[r][c] - f * A[i][c] for c in range(n)]
                b[r] -= f * b[i]
    return [b[i] / A[i][i] for i in range(n)]


def fit_lean(resdir, quiet=False, quad=False):
    """Least squares on results/lean-verify.tsv (np-lean-verify, 1 core, min of 3)."""
    import os
    rows = read_tsv(os.path.join(resdir, "lean-verify.tsv"))
    X, y = [], []
    for r in rows:
        B, ood, nt = int(r["proof_B"]) / 1e6, int(r["ood"]), int(r["ntables"])
        X.append([1.0, B, ood] + ([nt * ood / 1e3] if quad else []))
        y.append(float(r["lean_ms_min"]))
    c = lstsq(X, y)
    if not quad:
        c = c + [0.0]
    if not quiet:
        print(f"Lean verify fit ({'with' if quad else 'no'} List term): t_ms = {c[0]:.1f} + {c[1]:.1f}*MB "
              f"+ {c[2]:.4f}*OOD + {c[3]:.4f}*ntables*OOD/1e3")
        for r, x, yy in zip(rows, X, y):
            f = c[0] + c[1] * x[1] + c[2] * x[2] + (c[3] * x[3] if quad else 0)
            print(f"  {r['label']:<28} measured {yy:6.0f}  fit {f:6.0f}")
    return c


def cmd_curves(resdir):
    fit = fit_lean(resdir, quiet=True)
    fitq = fit_lean(resdir, quiet=True, quad=True)
    ops_per_tgas = 1e12 / REGULAR_OP_COST
    s_gas = math.ceil(GAS_MAX / REGULAR_OP_COST / OPS_PER_SEG)
    print(f"ops per Tgas = {ops_per_tgas:.4g}; ops per segment = {OPS_PER_SEG} = "
          f"{OPS_PER_SEG / ops_per_tgas:.3f} Tgas; 10^15 gas -> S = {s_gas}")
    pa, pt = PROVE_S_PER_WEQ22["near-anchor"], PROVE_S_PER_WEQ22["toy-anchor"]
    for preset in PRESETS:
        seg = PRESETS[preset]
        b1 = proof_bytes(r1_air(1, preset))
        b2 = proof_bytes(r1_air(2, preset))
        per = b2 - b1
        base = b1 - per
        print(f"\n== preset {preset}: per-segment W_eq {weq(seg):.0f}, OOD {ood_count(seg)}; "
              f"bytes(S) = {base:,.0f} + {per:,.0f}*S")
        for cap, nm in ((CAP_8MIB, "8 MiB"), (CAP_64MIB, "64 MiB")):
            smax = math.floor((cap - base) / per)
            print(f"   {nm} cap: S <= {smax}  ({smax * OPS_PER_SEG / ops_per_tgas:.1f} Tgas of WASM ops)")
        # verify cap 10 s and prove cap 600 s
        sv = max(S for S in range(1, 5000) if lean_verify_ms(r1_air(S, preset), fit) <= 10_000)
        sp = math.floor(600 / (pa * weq(seg)))
        print(f"   10 s Lean-verify cap: S <= {sv}; 600 s prove cap: S <= {sp} (near anchor), "
              f"{math.floor(600 / (pt * weq(seg)))} (toy anchor)")
        inter = sum(2 ** 22 * t["f"] for t in seg)
        glob = sum(2 ** 22 * t["f"] for t in GLOBAL)
        for bb in (36, 40, 46):
            sfp = (2 ** bb / MSG_LEN_P1 - glob) / inter
            print(f"   Air.wf busBudget 2^{bb}: fpBound allows S <= {math.floor(sfp)}")
        print("   S\tMiB\tverify_s\tverify_s(+List)\tprove_h(near..toy)\tRSS_now_GB\tcost_fUSD\tW*_MiB")
        for S in (1, 8, 64, 512, 1000, s_gas):
            ts = r1_air(S, preset)
            b = proof_bytes(ts)
            v = lean_verify_ms(ts, fit, b) / 1e3
            vq = lean_verify_ms(ts, fitq, b) / 1e3
            p0, p1 = pa * weq(ts), pt * weq(ts)
            rss = 3.4 + 1.18 * 4 * S * weq(seg) / 310   # d3b-h20 slope, scaled to 2^22
            c = cost_fusd(p0, v, b)
            # reference: re-execution of the same gas; break-even witness size W*
            gas = S * OPS_PER_SEG * REGULAR_OP_COST
            vref = gas / REEXEC_GAS_PER_S
            wstar = (c - N_V * C_CPU * V_V * vref) / (N_V * C_BW)
            print(f"   {S}\t{b / 2**20:.2f}\t{v:.2f}\t{vq:.2f}\t{p0 / 3600:.2f}..{p1 / 3600:.2f}"
                  f"\t{rss:.0f}\t{c:.3g}\t{wstar / 2**20:.1f}")
        # per-segment cost shares
        b = per
        v = lean_verify_ms(r1_air(2, preset), fit) - lean_verify_ms(r1_air(1, preset), fit)
        p = pa * weq(seg)
        parts = (C_CPU * V_P * p, N_V * C_CPU * V_V * v / 1e3, N_V * b * C_BW)
        tot = sum(parts)
        print(f"   per-segment marginal cost {tot:.3g} fUSD: prove {100 * parts[0] / tot:.0f}%, "
              f"verify {100 * parts[1] / tot:.0f}%, bandwidth {100 * parts[2] / tot:.0f}%; "
              f"reexec verify of the same gas {N_V * C_CPU * V_V * OPS_PER_SEG * REGULAR_OP_COST / REEXEC_GAS_PER_S:.3g} fUSD")


def main():
    import os
    resdir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    if cmd == "check":
        cmd_check(resdir)
    elif cmd == "fit":
        fit_lean(resdir)
        fit_lean(resdir, quad=True)
    elif cmd == "curves":
        cmd_curves(resdir)
    elif cmd == "detail":
        for lab, ts in (("near max", NEAR_MAX),) + tuple((p, r1_air(1, p)) for p in PRESETS):
            d = proof_bytes(ts, detail=True)
            print(lab, {k: round(v) for k, v in d.items()})


if __name__ == "__main__":
    main()
