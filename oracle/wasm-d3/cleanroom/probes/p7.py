from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G, rec=None): c.append((l, f"{gas} {h}" + (f" {rec}" if rec else "")))
TAB = section(4, vec([b"\x70\x00\x04"]))
def b(code, locs=b"\x00", extra=()):
    return m(T, imp(VR), FN, TAB, MEM, EXP(), *extra, CODE(code, locs))
L1 = b"\x01\x01\x7f"
cnt = lambda k: b"\x41" + sleb(k) + b"\x21\x00"
# loop body starting with a bulk op (targeted loop)
loopbulk = cnt(3) + b"\x03\x40" + b"\x41\x00\x41\x00\x41\x05\xfc\x0b\x00" + b"\x20\x00\x41\x01\x6b\x22\x00\x0d\x00\x0b\x0b"
for g in [10**13, 125_000_000, 140_000_000, 160_000_000, 200_000_000, 250_000_000]:
    add(f"loop starting with memory.fill gas={g}", b(loopbulk, L1), g)
# nested targeted loops
nested = cnt(2) + b"\x03\x40\x03\x40\x20\x00\x41\x01\x6b\x22\x00\x0d\x01\x0b\x0b\x0b"
for g in [10**13, 120_000_000, 125_000_000, 130_000_000]:
    add(f"nested loops gas={g}", b(nested, L1), g)
# else after dead then-branch, end after dead
dead = b"\x41\x01\x04\x40\x0c\x00\x41\x05\x1a\x05\x41\x06\x1a\x0b\x41\x07\x1a\x02\x40\x0c\x00\x41\x01\x1a\x0b\x41\x02\x1a\x0b"
add("dead regions", b(dead))
# block untargeted with return inside
add("return in block", b(b"\x02\x40\x41\x01\x1a\x0f\x0b\x41\x02\x1a\x0b"))
# br_if to function label
add("br_if to function label", b(b"\x41\x01\x0d\x00\x41\x02\x1a\x0b"))
add("br_table to function label", b(b"\x02\x40\x41\x01\x0e\x01\x00\x01\x0b\x41\x02\x1a\x0b"))
# dead branch targeting a block (quirk)
add("dead br targets block", b(b"\x02\x40\x41\x01\x1a\x0f\x0c\x00\x0b\x41\x02\x1a\x0b"))
# GasLimitExceeded window near 1e15 (prepaid = 1e15)
pure = b"\x41\x00\x21\x00" * 200
for g in [10**15, 10**15 - 1]:
    add(f"prepaid {g}", b(pure, L1), g)
# memory.grow huge count -> GasLimitExceeded variant
add("memory.grow 2^32-1", b(b"\x41\x7f\x40\x00\x1a\x0b"))
add("memory.grow 1024 ok", b(b"\x41\x80\x08\x40\x00\x1a\x0b"))
add("memory.grow 1025", b(b"\x41\x81\x08\x40\x00\x1a\x0b"))
add("table.grow 9996 (cap 10000)", b(b"\xd0\x70\x41" + sleb(9996) + b"\xfc\x0f\x00\x1a\x0b"))
add("table.grow 9997 (cap 10000)", b(b"\xd0\x70\x41" + sleb(9997) + b"\xfc\x0f\x00\x1a\x0b"))
# env.gas
GAS_T = section(1, vec([functype([I64, I64], []), functype([], []), functype([I32], [])]))
gimp = imp(VR, name("env") + name("gas") + b"\x00\x02")
for k in [0, 1, 1000, 2**31, 2**32 - 1]:
    add(f"env.gas({k})", m(GAS_T, gimp, FN, MEM, EXP(2), CODE(b"\x41" + sleb(k - 2**32 if k >= 2**31 else k) + b"\x10\x01\x0b")))
# value_return with receivers and too-long data
vr = lambda n, p=0: b"\x42" + sleb(n) + b"\x42" + sleb(p) + b"\x10\x00\x0b"
add("vr 5e6 bytes + receivers", b(vr(5_000_000)), G, "bob.near")
add("vr 5e6 bytes + receivers lowgas", b(vr(5_000_000)), 3 * 10**13, "bob.near,alice.near")
add("vr 4194304 bytes + receivers", b(vr(4194304)), G, "bob.near")
add("vr 4194305 bytes", b(vr(4194305)), G)
add("vr oob ptr", b(vr(8, 2**26 - 4)), G)
add("vr len u64max", b(vr(-1, 5)), G)
add("vr ptr+len overflow", b(vr(16, -8)), G)
add("vr empty", b(vr(0)), G)
add("vr twice", b(b"\x42\x02\x42\x00\x10\x00" + vr(3, 1)), G)
add("vr receivers lowgas fail", b(vr(65536)), 4 * 10**11, "bob.near,carol.near,alice.near")
# stack exhaustion: recursion
T3 = section(1, vec([functype([I64, I64], []), functype([], [])]))
rec_body = b"\x10\x01\x0b"
add("infinite recursion", m(T3, imp(VR), FN, MEM, EXP(), CODE(rec_body)))
add("infinite recursion low gas", m(T3, imp(VR), FN, MEM, EXP(), CODE(rec_body)), 10**10)
add("infinite recursion w/ locals", m(T3, imp(VR), FN, MEM, EXP(), CODE(rec_body, b"\x01\x64\x7e")))
# start function consumes gas then main
add("start + main", m(T3, imp(VR), section(3, vec([uleb(1), uleb(1)])), MEM, EXP(), section(8, uleb(2)), section(10, vec([b"\x05\x00\x41\x00\x1a\x0b", b"\x02\x00\x0b"]))))
add("start runs out of gas", m(T3, imp(VR), section(3, vec([uleb(1), uleb(1)])), MEM, EXP(), section(8, uleb(2)), section(10, vec([b"\x02\x00\x0b", b"\x09\x00\x03\x40\x0c\x00\x0b\x0b"[0:0] + b"\x07\x00\x03\x40\x0c\x00\x0b\x0b"]))), 10**10)
# no-main + data segment OOB
add("no-main + data OOB", m(T, imp(VR), FN, MEM, section(7, vec([name("x") + b"\x00\x01"])), CODE(), section(11, vec([b"\x00\x41" + sleb(2**26 - 1) + b"\x0b" + vec([b"\x01", b"\x02"])]))))
add("bad-sig main + elem OOB", m(section(1, vec([functype([I64, I64], []), functype([I32], [])])), imp(VR), FN, TAB, MEM, EXP(), section(9, vec([b"\x00\x41\x04\x0b" + vec([uleb(1)])])), CODE()))
add("data OOB zero length at end", m(T, imp(VR), FN, MEM, EXP(), CODE(), section(11, vec([b"\x00\x41" + sleb(2**26) + b"\x0b" + vec([])]))))
add("data OOB zero length past end", m(T, imp(VR), FN, MEM, EXP(), CODE(), section(11, vec([b"\x00\x41" + sleb(2**26 + 1) + b"\x0b" + vec([])]))))
add("elem OOB zero length past end", m(T, imp(VR), FN, TAB, MEM, EXP(), section(9, vec([b"\x00\x41\x05\x0b" + vec([])])), CODE()))
add("elem ok then data OOB", m(T, imp(VR), FN, TAB, MEM, EXP(), section(9, vec([b"\x00\x41\x01\x0b" + vec([uleb(1)])])), CODE(), section(11, vec([b"\x00\x41\x7f\x0b" + vec([b"\x01"])]))))
add("data OOB with gas below fee", m(T, imp(VR), FN, MEM, EXP(), CODE(), section(11, vec([b"\x00\x41\x7f\x0b" + vec([b"\x01"])]))), 10**8)
cmp(c)
