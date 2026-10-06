from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G): c.append((l, f"{gas} {h}"))
T2 = section(1, vec([functype([I64, I64], []), functype([], []), functype([I32] * 65, [])]))
EXPS = lambda nm, kind=0, idx=1: section(7, vec([name("main") + b"\x00\x01", name(nm) + bytes([kind]) + uleb(idx)]))
big = "x" * 100000
add("long export + 65-param fn", m(T2, imp(VR), section(3, vec([uleb(1), uleb(2)])), MEM, EXPS(big), section(10, vec([b"\x02\x00\x0b"] * 2))))
add("long export + opstack too large", m(T, imp(VR), FN, MEM, EXPS(big), CODE(b"\x42\x00" * 1025 + b"\x1a" * 1025 + b"\x0b")))
add("long export + bad body", m(T, imp(VR), FN, MEM, EXPS(big), CODE(b"\xff\x0b")))
add("long export + 5001 blocks", m(T, imp(VR), FN, MEM, EXPS(big), CODE(b"\x02\x40\x0b" * 5001 + b"\x0b")))
add("long export + engine locals", m(T, imp(VR), FN, MEM, EXPS(big), CODE(b"\x0b", b"\x01" + uleb(49999) + b"\x7f")))
add("long export name memory", m(T, imp(VR), FN, MEM, EXPS(big, 2, 0), CODE()))
add("long export name global", m(T, imp(VR), FN, MEM, section(6, vec([b"\x7f\x00\x41\x00\x0b"])), EXPS(big, 3, 0), CODE()))
add("export name 99999", m(T, imp(VR), FN, MEM, EXPS("x" * 99999), CODE()))
add("import name 100000", m(T, imp(VR, name("env") + name(big) + b"\x00\x01"), FN, MEM, EXP(2), CODE()))
add("long export, gas 0", m(T, imp(VR), FN, MEM, EXPS(big), CODE()), 0)
add("long export + too many tables", m(T, imp(VR), FN, section(4, vec([b"\x70\x00\x01"] * 2)), MEM, EXPS(big), CODE()))
cmp(c)
