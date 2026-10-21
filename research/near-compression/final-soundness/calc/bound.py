#!/usr/bin/env python3
"""Historical parameter calculation; NOT an established security bound.

The family constants and recursive model used below are unproved/withdrawn.
These are historical study shapes, not the measured G2 VK. Use audit_g2.py for
artifact checks and exact query arithmetic; neither script establishes security.

Evaluates every term of PROOF.md:
  * the per-move round-by-round knowledge (rbr-KS) errors of one SWIRL layer
    (LogUp, GKR, zerocheck, stacking, WHIR with x15 domains, m = 3, k1, keep-domain,
    grinding z inside the query move), Lemmas 3.1-3.9 and 4.1-4.6;
  * the WHIR query schedule exactly as the backend computes it
    (WhirConfig::new, unified tree config.rs:405-457);
  * the QROM Fiat-Shamir / straight-line extraction bound (Theorem 6.1, the K = 0 case of
    weak-binding Theorem 4, extended in PROOF.md section 6), with the counter-mode
    simulation factor t -> 2t of Lemma 6.3;
  * cross-checks: CMS19 Thm 8.6 constants and CDHZ (ePrint 2025/2166) Thm 11.3 + 6.10.

Checks that the historical formula evaluates below 2^-128; this is only an
arithmetic regression. --require-security exits 2 because proof obligations remain.

Default regime: **U-13** (user decision 2026-10-18; MCA-UPGRADE.md).  The proximity inputs of
PROOF.md section 4 come from DKT26 (ePrint 2026/2056; Lean: github.com/quangvdao/ArkLib @ a5aa2677):
final and inner NV layers at the first-order certified agreements of dkt_certs.json (O-2), base
layer at the Johnson radius sqrt(rho)(1+1/128) (backend ListDecoding m = 64, O-1); mu batching by
first-order powers-curve certificates.  The per-move errors are evaluated by bound_mca.layer.
`--bcgm` reproduces the superseded BCGM Thm 9.2, m = 3 accounting (the functions below).
Stdlib only.  Usage:  python3 -I bound.py [--bcgm]   (writes nothing; prints the table)
"""
import math

LOG2 = math.log2
P = 15 * 2**27 + 1
LOG_F = 12 * LOG2(P)                 # |Ext12| = p^12 = 2^370.88
T_LOG = 64                           # adversary: 2^64 quantum queries to SHA-384
TARGET = 268                         # backend security_bits (per-round target)
Z = 32                               # query-phase grinding bits (wide 2-element witness)
M_LIST = 3                           # list-decoding multiplicity m (Johnson regime)
C_ODD = 15                           # x15 evaluation domains
NARROW = 336                         # 42-byte truncated Merkle digests
WIDE = 384                           # FS state (never truncated)
L_SKIP = 2
J_LOG = 20                           # max squeeze blocks per verifier move (cap; Lemma 6.3)
LV_LOG = 16                          # log2 of #hash points the final verifier evaluates (<= 2^16)
GOAL = -128


def lg(x):
    return LOG2(x) if x > 0 else -math.inf


def lsum(*xs):
    """log2 of a sum of 2^x terms."""
    m = max(xs)
    if m == -math.inf:
        return m
    return m + LOG2(sum(2 ** (x - m) for x in xs))


# ----------------------------------------------------------------------------------------
# WHIR schedule, exactly as config.rs:405-478 (unified tree)
# ----------------------------------------------------------------------------------------
def whir_schedule(log_h, b, k1, k, lf, keep_domain=True, c=C_ODD, target=TARGET, z=Z, m=M_LIST):
    n_rounds = 1 + math.ceil((log_h - k1 - lf) / k) if k1 else math.ceil((log_h - lf) / k)
    ks = [k1 if (i == 0 and k1) else k for i in range(n_rounds)]
    assert log_h - sum(ks) == lf, (log_h, ks, lf)
    lir, log_dom, mvars = b, log_h + b, log_h
    rounds = []
    for i, ki in enumerate(ks):
        log_rho = -lir - LOG2(c)                      # rho_i = 2^-lir_i / c
        alpha = 2 ** (log_rho / 2) * (1 + 1 / (2 * m))  # = 1 - delta_i (config.rs:332-346)
        bits = -LOG2(alpha)
        q = math.ceil((target - z) / bits)            # protocol_security_level = target - z
        rounds.append(dict(i=i, k=ki, lir=lir, log_rho=log_rho, log_alpha=LOG2(alpha),
                           q=q, log_n=LOG2(c) + log_dom, mvars=mvars,
                           log_list=LOG2(m) - log_rho))  # Johnson list size m/rho
        lir += ki - (0 if keep_domain else 1)
        log_dom -= (0 if keep_domain else 1)
        mvars -= ki
    return rounds


def log_mca(d, log_n, log_rho, m=M_LIST):
    """BCGM ePrint 2025/2051 Def 9.1 / Thm 9.2: (m+1/2)^7 / (3 rho^{3/2}) * d * n^2 / |F|."""
    return LOG2((m + 0.5) ** 7 / 3) - 1.5 * log_rho + lg(d) + 2 * log_n - LOG_F


# ----------------------------------------------------------------------------------------
# One SWIRL layer: every verifier move, PROOF.md sections 3-4
# ----------------------------------------------------------------------------------------
def layer_moves(s):
    sch = whir_schedule(s['log_h'], s['b'], s['k1'], s['k'], s['lf'], s.get('keep', True))
    r0 = sch[0]
    # PIOP moves happen before any WHIR OOD sample: union over the round-0 interleaved list
    lst0 = r0['log_list'] * s.get('commits', 1)
    mv = []

    def add(name, log_err):
        mv.append((name, log_err))

    N, ml = s['log_int'], s['msg_len']
    add('logup alpha,beta (L3.1)', lst0 + lsum(lg(ml) + 2 * N - 1, 1 + N) - LOG_F)
    add('gkr sumcheck round + xi coordinate (L3.2, L3.3)', lst0 + lg(3 + 2 ** L_SKIP) - LOG_F)
    add('gkr lambda_j / mu_j (L3.2)', lst0 + lg(1 + 2 ** L_SKIP) - LOG_F)
    add('constraint batching lambda (L3.4)', lst0 + lg(s['n_constraints'] - 1) - LOG_F)
    add('claim batching mu (L3.4)', lst0 + lg(3 * s['airs'] - 1) - LOG_F)
    d = s['degree']
    add('zerocheck univariate round r_0 (L3.5)', lst0 + lg((d + 1) * (2 ** L_SKIP - 1)) - LOG_F)
    add('zerocheck multilinear round (L3.5)', lst0 + lg(d + 1) - LOG_F)
    add('stacking lambda (L3.7)', lst0 + lg(2 * s['cols'] - 1) - LOG_F)
    add('stacking univariate u_0 (L3.7)', lst0 + lg(2 * (2 ** L_SKIP - 1)) - LOG_F)
    add('stacking round u_j (L3.7)', lst0 + lg(2) - LOG_F)
    W = s['W']
    add('whir mu batching, MCA d=W-1 (L4.2)',
        lsum(log_mca(W - 1, r0['log_n'], r0['log_rho']), r0['log_list'] + lg(W - 1) - LOG_F))
    for j, r in enumerate(sch):
        last = j == len(sch) - 1
        for sub in range(1, r['k'] + 1):
            ln = r['log_n'] - (sub - 1)        # conservative: unfolded size of that sub-round
            add(f'whir fold r{j}.{sub} (L4.3)',
                lsum(log_mca(1, ln, r['log_rho']), r['log_list'] + lg(3) - LOG_F))
        if not last:
            nx = sch[j + 1]
            add(f'whir OOD r{j + 1} (L4.4)', 2 * nx['log_list'] - 1 + nx['mvars'] - LOG_F)
        add(f'whir query r{j} incl. grinding z={Z} (L4.5, L5.1)', -Z + r['q'] * r['log_alpha'])
        if last:
            add(f'whir final gamma r{j} (L4.6)', lg(r['q'] + 1) - LOG_F)
        else:
            add(f'whir gamma r{j} (L4.6)', sch[j + 1]['log_list'] + lg(r['q'] + 1) - LOG_F)
    return sch, mv


# Shapes.  NV fixed point from lane/pq-recursion-sha384 extrapolate_nv2.py (268 / z = 32 /
# 42 B row): cells 2^26.13, interactions 2^24.34, 4 AIRs, 259 opened columns (193 rotated),
# max constraint degree 21 (k = 3 SHA AIR).  The penultimate shape is the one the model
# chooses for every inner NV layer.  The base (app) layer is NOT specified anywhere yet;
# a stress shape with W = 601 (the widest stacked width in x15-domains SOUNDNESS.md) is used.
NV_COMMON = dict(log_int=24.34, msg_len=16, n_constraints=4096, airs=4, degree=21, cols=259 + 193)
SHAPES = {
    'final (layer d)':         dict(NV_COMMON, log_h=19, b=8, k1=1, k=3, lf=9, W=141,
                                    expect_q=[42, 38, 31, 26]),
    'inner NV (layers 1..d-1)': dict(NV_COMMON, log_h=19, b=6, k1=1, k=4, lf=6, W=141,
                                    expect_q=[50, 46, 33, 26]),
    'base app (layer 0, stress)': dict(log_int=26, msg_len=32, n_constraints=2**14, airs=64,
                                       degree=21, cols=4096, log_h=21, b=6, k1=1, k=4, lf=8,
                                       W=601, commits=2),
}


def fs_bound_k0(log_eps, t_log, factor=2):
    """Theorem 6.1 (K = 0): Pr <= (t' G + sqrt(l_V / N))^2, t' = factor * t (Lemma 6.3),
    G^2 = 10 max(3t'/2^336, eps + J(2t'+1)/2^384)."""
    tl = t_log + LOG2(factor)
    # narrow points: |Chg| <= 3t' (outputs, both child halves of node inputs, absorbed roots;
    # no position indexing); challenge points: eps + J (2t'+1)/2^384 with J <= 2^20 blocks/move
    g2 = LOG2(10) + max(LOG2(3) + tl - NARROW, lsum(log_eps, J_LOG + tl + 1 - WIDE))
    amp = lsum(tl + g2 / 2, (LV_LOG - NARROW) / 2)
    return 2 * amp


def cms19(log_eps, t_log):
    """CMS19 Thm 8.6 explicit form 6(t^2 eps + 4 t^3 / 2^lambda) (shape caveats: GAPS.md)."""
    return LOG2(6) + lsum(2 * t_log + log_eps, 2 + 3 * t_log - NARROW)


def cdhz(log_eps, t_log, k_rounds=200):
    """CDHZ ePrint 2025/2166 Thm 11.3 with Thm 6.10 and Thm 8.3, w <= t, sigma = 336
    (one-call rnd_i per round, full-prefix FS inputs: see GAPS.md G-6)."""
    t = t_log
    sr = lsum(LOG2(80) + LOG2(2 ** t + k_rounds + 1) + LOG2(2 ** t + k_rounds) + log_eps,
              LOG2(2 ** t + k_rounds + 1) + LOG2(k_rounds) - WIDE)  # r_min >= 384 (one-call blocks)
    t2 = t + 1
    extract = LOG2(8 * 2**20 * 2**27) - NARROW
    offline = lsum(LOG2(160) + t + 2 * t2 - NARROW, LOG2(16 * 2**16 * 31) - NARROW)
    online = LOG2(240) + t + 2 * t2 - NARROW
    return lsum(2 + sr, 2 + extract, 3 + offline, 2 + online)


U13_EXPECT_Q = {'final (layer d)': [38, 35, 29, 24], 'inner NV (layers 1..d-1)': [45, 41, 31, 24],
                'base app (layer 0, stress)': [48, 44, 32, 25]}


def main_u13():
    import json
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import bound_mca as BM
    plans = json.load(open(BM.CERTS))['_plans']
    pl = {'final (layer d)': (plans['final']['plan'], plans['final']['batching']),
          'inner NV (layers 1..d-1)': (plans['inner NV']['plan'], plans['inner NV']['batching']),
          'base app (layer 0, stress)': ([('J', 64)] * 4, 'first-curve')}
    print(f"U-13: |F| = 2^{LOG_F:.2f};  t = 2^{T_LOG};  target {TARGET} = {TARGET - Z} query bits + z = {Z};"
          f"  x{C_ODD} domains;  digests {NARROW} b;  FS state {WIDE} b\n")
    worst_all = (-math.inf, '')
    for name, s in SHAPES.items():
        plan, bt = pl[name]
        res = BM.layer(s, [tuple(x) for x in plan], bt)
        assert res['q'] == U13_EXPECT_Q[name], (name, res['q'])
        print(f"== {name}: log_h={s['log_h']} b={s['b']} k1={s['k1']} k={s['k']} lf={s['lf']} W={s['W']}  "
              f"queries {res['q']}  OOD {res['u']}  batching {bt}")
        for r in res['rounds']:
            print(f"   round {r['i']}: {r['reg']}({r['par']}) rho=2^{math.log2(r['kdim'] / r['n']):.2f} n=2^{math.log2(r['n']):.2f} "
                  f"A={r['A']} a=2^{r['log_a']:.3f} q={r['q']} -> {-r['q'] * r['log_a']:.2f} + z;  list <= 2^{r['log_list']:.2f}")
        for nm, e in sorted(res['moves'], key=lambda x: -x[1])[:8]:
            print(f"   {e:9.2f}  {nm}")
        print(f"   worst move: {res['worst'][1]}  2^{res['worst'][0]:.2f}\n")
        if res['worst'][0] > worst_all[0]:
            worst_all = (res['worst'][0], f"{name}: {res['worst'][1]}")
    eps = worst_all[0]
    tot = fs_bound_k0(eps, T_LOG)
    print(f"eps_rbr-KS (max over all moves of all layers) = 2^{eps:.2f}   [{worst_all[1]}]")
    print(f"WITHDRAWN formula (unestablished premises): value = 2^{tot:.2f};  conservative union over 7 layers 2^{tot + LOG2(7):.2f}")
    print(f"   cross-checks: CMS19 2^{cms19(eps, T_LOG):.2f};  CDHZ 2^{cdhz(eps, T_LOG):.2f}")
    margin = GOAL - (tot + LOG2(7))
    print(f"{'FORMULA BELOW TARGET' if margin >= 0 else 'FORMULA ABOVE TARGET'}: value <= 2^{GOAL} with {margin:.2f} bits margin (7-layer union), "
          f"NOT a security result; see GAPS.md for unproved premises and the retired A-IC model.")
    assert margin >= 0


def main():
    print(f"|F| = 2^{LOG_F:.2f};  t = 2^{T_LOG};  target {TARGET} = {TARGET - Z} query bits + z = {Z};"
          f"  m = {M_LIST};  x{C_ODD} domains;  digests {NARROW} b;  FS state {WIDE} b\n")
    worst_all = (-math.inf, '')
    for name, s in SHAPES.items():
        sch, mv = layer_moves(s)
        qs = [r['q'] for r in sch]
        if 'expect_q' in s:
            assert qs == s['expect_q'], (name, qs, s['expect_q'])
        print(f"== {name}: log_h={s['log_h']} b={s['b']} k1={s['k1']} k={s['k']} lf={s['lf']} "
              f"W={s['W']}  queries {qs}" + ("  (= backend schedule)" if 'expect_q' in s else ""))
        for r in sch:
            print(f"   round {r['i']}: k={r['k']} rho=2^{r['log_rho']:.2f} n=2^{r['log_n']:.2f} "
                  f"1-delta=2^{r['log_alpha']:.3f} q={r['q']} -> query bits {-r['q'] * r['log_alpha']:.2f}"
                  f" + z = {-r['q'] * r['log_alpha'] + Z:.2f};  list m/rho = 2^{r['log_list']:.2f}")
        mv_sorted = sorted(mv, key=lambda x: -x[1])
        seen = set()
        for nm, e in mv_sorted:
            key = nm.split(' r')[0] if nm.startswith('whir fold') else nm
            if key in seen and nm.startswith('whir fold'):
                continue
            seen.add(key)
            print(f"   {e:9.2f}  {nm}")
        w = mv_sorted[0]
        print(f"   worst move: {w[0]}  2^{w[1]:.2f}\n")
        if w[1] > worst_all[0]:
            worst_all = (w[1], f"{name}: {w[0]}")

    eps = worst_all[0]
    print(f"eps_rbr-KS (max over all moves of all layers) = 2^{eps:.2f}   [{worst_all[1]}]")
    tot = fs_bound_k0(eps, T_LOG)
    print("\nWITHDRAWN family formula (unestablished premises):")
    print(f"   t' = 2t (Lemma 6.3) ; G^2 = 10 max(3t'/2^{NARROW}, eps + 2^{J_LOG}(2t'+1)/2^{WIDE})")
    print(f"   historical formula value = 2^{tot:.2f}")
    for d in (6, 7):
        print(f"   conservative union over d+1 = {d + 1} layers: 2^{tot + LOG2(d + 1):.2f}")
    print("\ncross-checks (not used for the claim):")
    print(f"   CMS19 Thm 8.6 constants 6(t^2 eps + 4t^3/2^336):        2^{cms19(eps, T_LOG):.2f}")
    print(f"   CDHZ Thm 11.3 + 6.10 + 8.3 (w <= t, k = 200 rounds):   2^{cdhz(eps, T_LOG):.2f}")
    print("\nhistorical sequential-squeeze snapshot (superseded by the G2 T* implementation):")
    no_grind = eps + Z
    print(f"   no proven grinding credit -> eps = 2^{no_grind:.2f} -> old formula gives "
          f"2^{fs_bound_k0(no_grind, T_LOG, factor=1):.2f}  (and even this needs the one-call model [H-M])")

    margin = GOAL - (tot + LOG2(7))
    print()
    if tot + LOG2(7) <= GOAL:
        print(f"FORMULA BELOW TARGET: value <= 2^{GOAL} with {margin:.2f} bits margin (conservative 7-layer union), "
              f"NOT a security result; family, sampler, WHIR and recursive-model obligations remain.")
    else:
        print(f"FORMULA ABOVE TARGET: value exceeds 2^{GOAL} by {-margin:.2f} bits")
    assert tot + LOG2(7) <= GOAL


if __name__ == '__main__':
    import sys
    print('HISTORICAL CALCULATION ONLY: security is NOT established; these are not the G2 parameters.\n')
    if '--bcgm' in sys.argv:
        main()
    else:
        main_u13()

    if '--require-security' in sys.argv:
        sys.exit(2)
