from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G): c.append((l, f"{gas} {h}"))
def bod(x, locs=b"\x00"): x = locs + x + b"\x0b"; return uleb(len(x)) + x
TP = section(1, vec([functype([I64, I64], []), functype([], []), functype([I32] * 64, []), functype([I32] * 17, []), functype([I32] * 65, [])]))
big = b"\x42\x00" * 1025 + b"\x1a" * 1025
blocks = b"\x02\x40\x0b" * 5001
add("import with 17 params + 781x64 defined", m(TP, imp(VR, name("env") + name("x") + b"\x00\x03"), section(3, vec([uleb(1)] + [uleb(2)] * 781)), MEM, EXP(2), section(10, vec([bod(b"")] * 782))))
add("import with 65 params", m(TP, imp(VR, name("env") + name("x") + b"\x00\x04"), FN, MEM, EXP(2), section(10, vec([bod(b"")]))))
add("5001 blocks mostly dead", m(T, imp(VR), FN, MEM, EXP(), section(10, vec([bod(b"\x0f" + blocks)]))))
add("opstack big only in dead code", m(T, imp(VR), FN, MEM, EXP(), section(10, vec([bod(b"\x0f" + big)]))))
add("opstack + 5001 blocks same fn", m(T, imp(VR), FN, MEM, EXP(), section(10, vec([bod(big + blocks)]))))
add("65 params + opstack same fn", m(TP, imp(VR), section(3, vec([uleb(1), uleb(4)])), MEM, EXP(), section(10, vec([bod(b""), bod(big)]))))
add("f0 opstack, f1 65 params", m(TP, imp(VR), section(3, vec([uleb(1), uleb(4)])), MEM, EXP(), section(10, vec([bod(big), bod(b"")]))))
add("f0 5001 blocks, f1 65 params", m(TP, imp(VR), section(3, vec([uleb(1), uleb(4)])), MEM, EXP(), section(10, vec([bod(blocks), bod(b"")]))))
add("f0 opstack, f1 engine locals", m(T, imp(VR), section(3, vec([uleb(1), uleb(1)])), MEM, EXP(), section(10, vec([bod(big), bod(b"", b"\x01" + uleb(49999) + b"\x7f")]))))
add("engine locals + too large instr? no; engine locals + LinkError", m(T, imp(VR, name("env") + name("nope") + b"\x00\x01"), section(3, vec([uleb(1)])), MEM, EXP(2), section(10, vec([bod(b"", b"\x01" + uleb(49999) + b"\x7f")]))))
add("engine locals with gas 0", m(T, imp(VR), FN, MEM, EXP(), section(10, vec([bod(b"", b"\x01" + uleb(49999) + b"\x7f")]))), 0)
cmp(c)
