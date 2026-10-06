from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G, rec=None): c.append((l, f"{gas} {h}" + (f" {rec}" if rec else "")))
GAS_T = section(1, vec([functype([I64, I64], []), functype([], []), functype([I32], [])]))
gimp = imp(VR, name("env") + name("gas") + b"\x00\x02")
L1 = b"\x01\x01\x7f"
K = 1215400000   # *R ~ 9.99968e14
pure = b"\x41\x00\x21\x00" * 300
code = b"\x41" + sleb(K - 2**32 if K >= 2**31 else K) + b"\x10\x01" + b"\x03\x40" + pure + b"\x0c\x00\x0b\x0b"
w = m(GAS_T, gimp, FN, MEM, EXP(2), CODE(code, L1))
import random
rr = random.Random(5)
for g in [10**15, 10**15 - 1, 10**15 - 10**8, 10**15 - 4 * 10**8] + [10**15 - rr.randrange(0, 10**9) for _ in range(12)]:
    add(f"window prepaid={g}", w, g)
cmp(c)
