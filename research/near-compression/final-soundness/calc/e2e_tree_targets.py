#!/usr/bin/env python3
"""Per-round rbr targets for a whole aggregation tree (lane E, M11e, 2026-11-03).

Arithmetic only; NOT a security bound. It backs docs/zk-formal/E2E-SOUNDNESS-BUDGET.md §9.
For each accounting of N proofs it prints the largest per-move rbr error eps that keeps the
total below 2^-128 at Q = 2^64. It then prints the WHIR query counts that reach that target on
the U-13 model shapes of bound.out. Per-query bits are -log2(a_i) at the certified agreements.

Usage:  python3 -I e2e_tree_targets.py      (stdlib only; imports bound.py from this directory)
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bound as B  # noqa: E402

T = 64
Z = 32
NS = {'D0a chain': 7, '1 Pgas design (137 leaves, fan-in 8)': 160, 'depth 6, fan-in 8 + wrap': 299594}


def l(*x):
    m = max(x)
    return m + math.log2(sum(2 ** (y - m) for y in x))


# The epsilon-free terms of bound.cdhz (CDHZ Thm 11.3 + 6.10 + 8.3, sigma = 336): extraction,
# offline and online. These are cubic hash terms of the form t^3 / 2^336 with constants.
t2 = T + 1
EX = 2 + math.log2(8 * 2**20 * 2**27) - 336
OFF = 3 + l(math.log2(160) + T + 2 * t2 - 336, math.log2(16 * 2**16 * 31) - 336)
ON = 2 + math.log2(240) + T + 2 * t2 - 336
FLOOR = l(EX, OFF, ON)
ROOM = math.log2(2**-128 - 2**FLOOR)
CDHZ_EPS_CONST = 2 + math.log2(80) + 2 * T      # the dominant (state-restoration) term

print(f"CDHZ at eps = 2^-268.01: 2^{B.cdhz(-268.01, T):.2f}; eps-free floor 2^{FLOOR:.2f}")
print(f"CMS19 Thm 8.6 constants at eps = 2^-268.01: 2^{B.cms19(-268.01, T):.2f}\n")
for name, n in NS.items():
    ln = math.log2(n)
    print(f"== {name}: N = {n} (2^{ln:.2f})")
    print(f"   per-proof, constants 1 (Q^2 eps per proof, Q^3/2^336 once): eps <= 2^{-(256 + ln):.2f}")
    print(f"   per-proof, CMS19 constants, whole bound per proof: total 2^{B.cms19(-268.01, T) + ln:.2f}")
    print(f"   per-proof, CDHZ, whole bound per proof: total 2^{B.cdhz(-268.01, T) + ln:.2f}"
          f" (floor alone 2^{FLOOR + ln:.2f})")
    print(f"   per-proof, CDHZ, eps term per proof, floor once: eps <= 2^{ROOM - ln - CDHZ_EPS_CONST:.2f}")

shapes = {'final': [6.214, 6.743, 8.140, 9.834], 'inner': [5.245, 5.759, 7.614, 9.835],
          'base': [4.942, 5.442, 7.442, 9.442]}
q0 = {'final': [38, 35, 29, 24], 'inner': [45, 41, 31, 24], 'base': [48, 44, 32, 25]}
print("\nWHIR queries per round needed (z = 32 kept); delta vs the bound.out schedules:")
for target in (268.0, 274.19, 282.73):
    for s, a in shapes.items():
        q = [math.ceil((target - Z) / x) for x in a]
        d = [x - y for x, y in zip(q, q0[s])]
        print(f"   target {target:6.2f}  {s:5s}  q = {q}  delta = {d} (+{sum(d)})")
    print(f"   target {target:6.2f}  z-only alternative: z = {Z + max(0, math.ceil(target - 268.0))}")


# ---- M11f (2026-11-04): lane D's D-8 tree (arity 4) at its recorded per-vk rbr errors ----------
# Per-vk calculator bits (research/near-compression/e2e/results/zk/d8/tree8/*/soundness.txt,
# base-whir.txt): wrap ns19lb6 [46,41,31,25] 268.2 (zk = 6; ZK-ARGUMENT sec. 5: masked moves keep
# the minimum, new nu move 295.6); node P_2/P_* ns20lb5 [54,41,31,25] 268.2; leaf ns20lb2
# [81,60,40,30] 268.5; D0a base class S/M ns18lb7 [44,35,27,23] 269.6, class L ns22lb2 268.5;
# lanes A/B segments seg-v1 [536,256,83,50,36] 268.2 at 24 grinding bits.
# PAD leaves/nodes prove fixed true statements: a forged PAD proof proves nothing false, so they
# are not charged.  Segments are proofs (checked in-circuit by their leaves) and are charged.
EPS = {'seg': -268.2, 'leaf': -268.5, 'node': -268.2, 'wrap': -268.2}
print("\n== M11f: D-8 tree, arity 4 (per-vk eps; segments + leaves + nodes + wrap) ==")
print(f"   wrap alone (one proof, family QROM): CDHZ 2^{B.cdhz(EPS['wrap'], T):.2f}, "
      f"CMS19 2^{B.cms19(EPS['wrap'], T):.2f}, constants 1 2^{l(2 * T + EPS['wrap'], 3 * T - 336):.2f}, "
      f"ROM 2^{l(T + EPS['wrap'], 2 * T - 337):.2f}")


def nodes(s, a=4):
    n, lv = 0, 0
    while s > 1:
        s = -(-s // a)
        n += s
        lv += 1
    return n, lv


for name, s in [('measured D-8 run (1 base, 1 real leaf + 3 PAD, 1 node)', 1),
                ('100 Tgas (25 segments, model)', 25), ('1 Pgas (94 segments, model)', 94),
                ('arity 4, depth 6 ceiling (4^6 segments)', 4 ** 6)]:
    nn, depth = nodes(s) if s > 1 else (1, 1)
    cnt = {'seg': s, 'leaf': s, 'node': nn, 'wrap': 1}
    tot = sum(cnt.values())
    c1 = l(*[math.log2(cnt[k]) + 2 * T + EPS[k] for k in cnt], 3 * T - 336)
    cm = l(*[math.log2(cnt[k]) + B.cms19(EPS[k], T) for k in cnt])
    rom = l(*[math.log2(cnt[k]) + T + EPS[k] for k in cnt], 2 * T - 337)
    need = -(256 + math.log2(tot))
    print(f"   {name}: depth {depth}, N = {tot} (seg {s}, leaf {s}, node {nn}, wrap 1) = 2^{math.log2(tot):.2f}")
    print(f"      per-proof union: constants 1 2^{c1:.2f} ({-c1:.1f} bits); CMS19 whole bound per proof "
          f"2^{cm:.2f} ({-cm:.1f} bits); ROM 2^{rom:.2f}; eps needed at constants 1: 2^{need:.2f}")
