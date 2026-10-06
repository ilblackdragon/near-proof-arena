from probe import *
exec(open("p3.py").read().split("c = []")[0])
c = []
def add(l, h, gas=G): c.append((l, f"{gas} {h}"))
T4 = section(1, vec([functype([I64, I64], []), functype([], []), functype([], [I32])]))
IMPS = imp(VR, name("env") + name("panic") + b"\x00\x01")
F2 = section(3, vec([uleb(1), uleb(2)]))      # main = 2, helper = 3 returns 42
TAB = section(4, vec([b"\x70\x00\x08"]))
H = b"\x04\x00\x41\x2a\x0b"
ret4 = b"\x36\x02\x00\x42\x04\x42\x00\x10\x00\x0b"   # store i32 at 0 then value_return 4 bytes
def mm(main, elems=None, extra=(), locs=b"\x00", glob=None):
    secs = [T4, IMPS, F2, TAB, MEM]
    if glob: secs.append(section(6, vec(glob)))
    secs.append(section(7, vec([name("main") + b"\x00\x02"])))
    if elems: secs.append(section(9, vec(elems)))
    body = locs + main
    secs.append(section(10, vec([uleb(len(body)) + body, H])))
    return m(*secs)
ci = lambda i: b"\x41\x00" + b"\x41" + sleb(i) + b"\x11\x02\x00" + ret4
add("elem flag2 explicit table", mm(ci(1), [b"\x02\x00\x41\x01\x0b\x00" + vec([uleb(3)])]))
add("elem flag4 exprs", mm(ci(2), [b"\x04\x41\x02\x0b" + vec([b"\xd2\x03\x0b", b"\xd0\x70\x0b"])]))
add("elem flag4 null entry call", mm(ci(3), [b"\x04\x41\x02\x0b" + vec([b"\xd2\x03\x0b", b"\xd0\x70\x0b"])]))
add("elem flag5 passive exprs + table.init", mm(b"\x41\x00\x41\x00\x41\x01\xfc\x0c\x00\x00" + ci(0), [b"\x05\x70" + vec([b"\xd2\x03\x0b"])]))
add("elem flag6 table expr reftype", mm(ci(4), [b"\x06\x00\x41\x04\x0b\x70" + vec([b"\xd2\x03\x0b"])]))
add("elem flag7 declarative exprs + ref.func", mm(b"\x41\x00\x41\x00\xd2\x03\x26\x00" + ci(0)[2:], [b"\x07\x70" + vec([b"\xd2\x03\x0b"])]))
add("elem flag 1 elemkind 0x01", mm(ci(1), [b"\x01\x01" + vec([uleb(3)])]))
add("elem flag 8", mm(ci(1), [b"\x08\x00" + vec([uleb(3)])]))
add("elem expr global.get", mm(ci(1), [b"\x04\x41\x02\x0b" + vec([b"\x23\x00\x0b"])], glob=[b"\x70\x00\xd0\x70\x0b"]))
add("elem flag4 i32 expr wrong type", mm(ci(1), [b"\x04\x41\x02\x0b" + vec([b"\x41\x00\x0b"])]))
add("call import via table (panic)", m(section(1, vec([functype([I64, I64], []), functype([], []), functype([], [I32])])), IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x02"])), section(9, vec([b"\x00\x41\x00\x0b" + vec([uleb(1)])])), section(10, vec([b"\x07\x00\x41\x00\x11\x01\x00\x0b", H]))))
add("call import via table wrong sig", mm(b"\x41\x00\x41\x00\x11\x02\x00" + ret4, [b"\x00\x41\x00\x0b" + vec([uleb(1)])]))
add("funcref global set/get + table.set", mm(b"\xd2\x03\x24\x00\x41\x05\x23\x00\x26\x00" + ci(5), [b"\x03\x00" + vec([uleb(3)])], glob=[b"\x70\x01\xd0\x70\x0b"]))
add("funcref local default null", mm(b"\x41\x00\x20\x00\xd1" + ret4, locs=b"\x01\x01\x70"))
add("typed select funcref", mm(b"\x41\x06\xd2\x03\xd0\x70\x41\x01\x1c\x01\x70\x26\x00" + ci(6), [b"\x03\x00" + vec([uleb(3)])]))
add("typed select funcref cond 0", mm(b"\x41\x06\xd2\x03\xd0\x70\x41\x00\x1c\x01\x70\x26\x00" + ci(6), [b"\x03\x00" + vec([uleb(3)])]))
add("table.get import ref is_null", mm(b"\x41\x00\x41\x00\x25\x00\xd1" + ret4, [b"\x00\x41\x00\x0b" + vec([uleb(0)])]))
add("br_table with value", mm(b"\x41\x00\x02\x7f\x02\x7f\x41\x07\x41\x01\x0e\x01\x00\x01\x0b\x41\x01\x6a\x0b" + ret4))
add("if/else with results", mm(b"\x41\x00\x41\x00\x04\x7f\x41\x01\x05\x41\x02\x0b" + ret4))
add("loop with result", mm(b"\x41\x00\x03\x7f\x41\x09\x0b" + ret4))
add("memory.init after data.drop n=0", m(T4, IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x02"])), section(12, uleb(1)), section(10, vec([b"\x0d\x00\xfc\x09\x00\x41\x00\x41\x00\x41\x00\xfc\x08\x00\x00\x0b", H])), section(11, vec([b"\x01" + vec([b"\x01"])]))))
add("memory.init active seg n=1", m(T4, IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x02"])), section(12, uleb(1)), section(10, vec([b"\x0b\x00\x41\x00\x41\x00\x41\x01\xfc\x08\x00\x00\x0b", H])), section(11, vec([b"\x00\x41\x00\x0b" + vec([b"\x01"])]))))
add("memory.copy overlap", mm(b"\x41\x00\x41\x01\x41\x08\xfc\x0a\x00\x00\x41\x00\x41\x00\x28\x02\x00" + ret4))
add("deep nesting 300 blocks", mm(b"\x02\x40" * 300 + b"\x0c\x96\x02" + b"\x0b" * 300 + b"\x41\x00\x41\x01" + ret4))
add("main export = helper with result (bad sig)", m(T4, IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x03"])), section(10, vec([b"\x02\x00\x0b", H]))))
add("start + main both export", m(T4, IMPS, F2, TAB, MEM, section(7, vec([name("main") + b"\x00\x02"])), section(8, uleb(2)), section(10, vec([b"\x02\x00\x0b", H]))))
cmp(c)
