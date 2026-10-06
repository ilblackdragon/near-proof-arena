from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G): c.append((l, f"{gas} {h}"))
T4 = section(1, vec([functype([I64, I64], []), functype([], []), functype([], [I32])]))
IMPS = imp(VR, name("env") + name("panic") + b"\x00\x01")
F2 = section(3, vec([uleb(1), uleb(2)])); TAB = section(4, vec([b"\x70\x00\x08"])); H = b"\x04\x00\x41\x2a\x0b"
def bod(x): x = b"\x00" + x; return uleb(len(x)) + x
def mi(code, seg):
    return m(T4, IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x02"])), section(12, uleb(1)), section(10, vec([bod(code), H])), section(11, vec([seg])))
Z = b"\x41\x00\x41\x00"
for n in [0, 1]:
    add(f"memory.init after data.drop n={n}", mi(b"\xfc\x09\x00" + Z + b"\x41" + sleb(n) + b"\xfc\x08\x00\x00\x0b", b"\x01" + vec([b"\x01"])))
    add(f"memory.init active seg n={n}", mi(Z + b"\x41" + sleb(n) + b"\xfc\x08\x00\x00\x0b", b"\x00\x41\x00\x0b" + vec([b"\x01"])))
    add(f"memory.init passive s=1 n={n}", mi(b"\x41\x00\x41\x01\x41" + sleb(n) + b"\xfc\x08\x00\x00\x0b", b"\x01" + vec([b"\x01"])))
    add(f"memory.init passive s=2 n={n}", mi(b"\x41\x00\x41\x02\x41" + sleb(n) + b"\xfc\x08\x00\x00\x0b", b"\x01" + vec([b"\x01"])))
cmp(c)
