#!/usr/bin/env python3
"""Per-opcode differential cases for the D3α integer subset (requirements v0.2 §2.2).

Each case is one contract whose `main` evaluates one operator on edge-value operands, stores the
result at memory[0..8) and returns it with `value_return`. Trapping inputs are their own cases.
Families: every i32/i64 unop/binop/relop/testop, wrap/extend/sign-ext, every load/store width at
the 64 MiB edge with offsets, memory.size/grow, memory.fill/copy/init and data.drop at bounds,
globals, select (typed and untyped), ref.null/is_null/func, table.get/set/size/grow/fill/copy/init,
elem.drop, call_indirect (ok, null, signature mismatch, out of bounds), br_table edges, and
preparation rejects for each NEAR limit.
Output: `<prepaid_gas> <hex>` per line, plus a sidecar `.labels` file naming each case.
"""
import sys
from wasmenc import *

GAS = 300 * 10**12
MEM = 1024 * 65536
E32 = [0, 1, 2, 3, 7, 8, 31, 32, 33, 0x7F, 0x80, 0xFF, 0x100, 0x7FFF, 0x8000, 0xFFFF, 0x10000,
       0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFE, 0xFFFFFFFF, 0x12345678, 0xDEADBEEF]
E64 = [0, 1, 2, 7, 63, 64, 65, 0x80, 0xFF, 0x8000, 0xFFFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF,
       0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0x8000000000000001,
       0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF, 0x0123456789ABCDEF, 0xFEDCBA9876543210]
SMALL32 = [0, 1, 2, 31, 32, 33, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 0x12345678, 0x80000001]
SMALL64 = [0, 1, 2, 63, 64, 65, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF,
           0xFFFFFFFFFFFFFFFE, 0x0123456789ABCDEF, 0x8000000000000001, 0x80000000, 0xFFFFFFFF]

cases = []


def emit(label, m, gas=GAS):
    cases.append((label, gas, m.encode().hex()))


def ret_i32(m, body_push):
    """body pushes an i32; store at 0 and return 4 bytes"""
    return i32c(0) + body_push + b"\x36\x02\x00" + value_return_tail(m, 4)


def ret_i64(m, body_push):
    return i32c(0) + body_push + b"\x37\x03\x00" + value_return_tail(m, 8)


def simple(label, is64_result, push, extra=None):
    m = base_module()
    if extra:
        extra(m)
    body = ret_i64(m, push) if is64_result else ret_i32(m, push)
    m.func([], [], [], body)
    m.exports.append(("main", 0, len(m.imports) + len(m.funcs) - 1))
    emit(label, m)


# ---- numeric
for op in [0x45, 0x67, 0x68, 0x69, 0xC0, 0xC1]:
    for a in E32:
        simple(f"i32.un.{op:#x}({a:#x})", False, i32c(a) + bytes([op]))
for op in [0x50, 0x79, 0x7A, 0x7B, 0xC2, 0xC3, 0xC4, 0xA7]:
    for a in E64:
        simple(f"i64.un.{op:#x}({a:#x})", op not in (0x50, 0xA7), i64c(a) + bytes([op]))
for op in [0xAC, 0xAD]:
    for a in E32:
        simple(f"i64.ext.{op:#x}({a:#x})", True, i32c(a) + bytes([op]))
for op in list(range(0x46, 0x50)) + list(range(0x6A, 0x79)):
    for a in SMALL32:
        for b in SMALL32:
            simple(f"i32.bin.{op:#x}({a:#x},{b:#x})", False, i32c(a) + i32c(b) + bytes([op]))
for op in list(range(0x51, 0x5B)) + list(range(0x7C, 0x8B)):
    for a in SMALL64:
        for b in SMALL64:
            simple(f"i64.bin.{op:#x}({a:#x},{b:#x})", 0x7C <= op, i64c(a) + i64c(b) + bytes([op]))

# ---- memory loads/stores (pattern data via active data segment at the 64 MiB edge and at 0)
PATTERN = bytes(range(0x80, 0x90))
LOADS = {0x28: (4, False), 0x29: (8, True), 0x2C: (1, False), 0x2D: (1, False), 0x2E: (2, False),
         0x2F: (2, False), 0x30: (1, True), 0x31: (1, True), 0x32: (2, True), 0x33: (2, True),
         0x34: (4, True), 0x35: (4, True)}
STORES = {0x36: (4, False), 0x37: (8, True), 0x3A: (1, False), 0x3B: (2, False), 0x3C: (1, True),
          0x3D: (2, True), 0x3E: (4, True)}
ALIGN = {1: 0, 2: 1, 4: 2, 8: 3}


def with_data(m):
    m.datas.append(b"\x00" + i32c(MEM - 16) + b"\x0b" + vec([bytes([x]) for x in PATTERN]))
    m.datas.append(b"\x00" + i32c(100) + b"\x0b" + vec([bytes([x]) for x in PATTERN]))


for op, (w, is64) in LOADS.items():
    for addr, off in [(100, 0), (100, 3), (MEM - 16, 0), (MEM - w, 0), (MEM - w + 1, 0), (MEM - 16, 16 - w),
                      (MEM - 16, 17 - w), (0xFFFFFFFF, 0), (0, 0xFFFFFFFF), (MEM, 0), (MEM - 1 - w, 1)]:
        simple(f"load.{op:#x}@{addr:#x}+{off}", is64,
               i32c(addr) + bytes([op]) + uleb(ALIGN[w]) + uleb(off), with_data)
for op, (w, is64) in STORES.items():
    for addr, off in [(200, 0), (MEM - w, 0), (MEM - w + 1, 0), (MEM - 8, 8 - w), (0xFFFFFFFF, 1)]:
        m = base_module()
        val = i64c(0x8877665544332211) if is64 else i32c(0x44332211)
        body = i32c(addr) + val + bytes([op]) + uleb(ALIGN[w]) + uleb(off)
        ra = (addr + off) & 0xFFFFFFFF
        ra = ra if ra + 8 <= MEM else 0
        body += value_return_tail(m, 8, ra)
        m.func([], [], [], body)
        m.exports.append(("main", 0, len(m.imports)))
        emit(f"store.{op:#x}@{addr:#x}+{off}", m)

# ---- memory.size / grow
for n in [0, 1, 1023, 1024, 1025, 0xFFFFFFFF, 0x80000000]:
    simple(f"memory.grow({n})", False, i32c(n) + b"\x40\x00" + b"\x3f\x00" + b"\x6a")

# ---- bulk memory (needs data count section for memory.init / data.drop)
for (d, s, n) in [(0, 100, 16), (MEM - 16, 0, 16), (MEM - 15, 0, 16), (0, MEM - 16, 16), (0, MEM - 15, 16),
                  (10, 12, 8), (12, 10, 8), (0, 0, 0), (MEM, 0, 0), (MEM + 1, 0, 0), (0, 0, 0xFFFFFFFF)]:
    m = base_module()
    with_data(m)
    m.func([], [], [], i32c(d) + i32c(s) + i32c(n) + b"\xfc\x0a\x00\x00" + value_return_tail(m, 32, 0))
    m.exports.append(("main", 0, len(m.imports)))
    emit(f"memory.copy({d:#x},{s:#x},{n:#x})", m)
for (d, v, n) in [(0, 0xAB, 16), (MEM - 16, 0x1FF, 16), (MEM - 15, 1, 16), (0, 0, 0), (MEM, 0, 0),
                  (MEM + 1, 0, 0), (5, 0xFFFFFFFF, 3)]:
    m = base_module()
    m.func([], [], [], i32c(d) + i32c(v) + i32c(n) + b"\xfc\x0b\x00" + value_return_tail(m, 32, 0))
    m.exports.append(("main", 0, len(m.imports)))
    emit(f"memory.fill({d:#x},{v:#x},{n:#x})", m)
for (d, s, n, drop) in [(0, 0, 4, False), (0, 2, 2, False), (0, 3, 2, False), (MEM - 4, 0, 4, False),
                        (MEM - 3, 0, 4, False), (0, 4, 0, False), (0, 5, 0, False), (0, 0, 1, True),
                        (0, 0, 0, True)]:
    m = base_module()
    m.datacount = True
    m.datas.append(b"\x01" + vec([b"\x01", b"\x02", b"\x03", b"\x04"]))   # passive
    body = (b"\xfc\x09\x00" if drop else b"") + i32c(d) + i32c(s) + i32c(n) + b"\xfc\x08\x00\x00"
    m.func([], [], [], body + value_return_tail(m, 8, 0))
    m.exports.append(("main", 0, len(m.imports)))
    emit(f"memory.init({d:#x},{s},{n},drop={drop})", m)

# ---- globals and select
for t, v in [(I32, 0xFFFFFFFF), (I64, 0x8000000000000000)]:
    m = base_module()
    init = (i32c(v) if t == I32 else i64c(v)) + b"\x0b"
    m.globals.append((t, True, init))
    upd = (i32c(5) + b"\x6a") if t == I32 else (i64c(5) + b"\x7c")
    body = b"\x23\x00" + upd + b"\x24\x00" + i32c(0) + b"\x23\x00" + (b"\x36\x02\x00" if t == I32 else b"\x37\x03\x00")
    m.func([], [], [], body + value_return_tail(m, 8, 0))
    m.exports.append(("main", 0, len(m.imports)))
    emit(f"global.{t:#x}", m)
for c in [0, 1, 0x80000000]:
    simple(f"select({c:#x})", False, i32c(11) + i32c(22) + i32c(c) + b"\x1b")
    simple(f"select_t64({c:#x})", True, i64c(11) + i64c(22) + i32c(c) + b"\x1c\x01\x7e")

# ---- tables, refs, call_indirect
CALLT0 = b"\x11\xee\x00"  # placeholder: call_indirect (type t0) table 0
def table_module(tmin, tmax, elems_active=True):
    m = base_module()
    t0 = m.type([], [I32])
    t1 = m.type([I32], [I32])
    f0 = m.func([], [I32], [], i32c(1111))                 # type ()->i32
    f1 = m.func([I32], [I32], [], b"\x20\x00" + i32c(1) + b"\x6a")
    m.tables.append((FUNCREF, tmin, tmax))
    if elems_active:
        m.elems.append(b"\x00" + i32c(0) + b"\x0b" + vec([uleb(f0), uleb(f1)]))   # table[0]=f0, [1]=f1
    m.elems.append(b"\x01\x00" + vec([uleb(f1), uleb(f0)]))                       # passive (index 1 or 0)
    m.elems.append(b"\x03\x00" + vec([uleb(f0)]))                                 # declarative
    return m, t0, t1, f0, f1


for idx in [0, 1, 2, 3, 9, 10, 0xFFFFFFFF]:
    for ty in ["t0", "t1"]:
        m, t0, t1, f0, f1 = table_module(4, 10)
        call = (i32c(idx) + b"\x11" + uleb(t0) + b"\x00") if ty == "t0" else \
            (i32c(41) + i32c(idx) + b"\x11" + uleb(t1) + b"\x00")
        m.func([], [], [], ret_i32(m, call))
        m.exports.append(("main", 0, len(m.imports) + len(m.funcs) - 1))
        emit(f"call_indirect[{idx}]:{ty}", m)
for (label, body_push) in [
        ("table.size", b"\xfc\x10\x00"),
        ("table.grow(0)", b"\xd0\x70" + i32c(0) + b"\xfc\x0f\x00"),
        ("table.grow(6)", b"\xd0\x70" + i32c(6) + b"\xfc\x0f\x00"),
        ("table.grow(7)", b"\xd0\x70" + i32c(7) + b"\xfc\x0f\x00"),
        ("table.grow(big)", b"\xd0\x70" + i32c(0xFFFFFFFF) + b"\xfc\x0f\x00"),
        ("table.get(1).is_null", i32c(1) + b"\x25\x00\xd1"),
        ("table.get(3).is_null", i32c(3) + b"\x25\x00\xd1"),
        ("table.get(4)", i32c(4) + b"\x25\x00\xd1"),
        ("ref.null.is_null", b"\xd0\x70\xd1"),
        ("ref.func.is_null", b"\xd2\x01\xd1"),
        ("table.set(3)+call", i32c(3) + b"\xd2\x01\x26\x00" + i32c(3) + CALLT0),
        ("table.set(4)", i32c(4) + b"\xd0\x70\x26\x00" + i32c(0)),
        ("table.fill(2,f0,2)+call", i32c(2) + b"\xd2\x01" + i32c(2) + b"\xfc\x11\x00" + i32c(3) + CALLT0),
        ("table.fill(3,null,2)", i32c(3) + b"\xd0\x70" + i32c(2) + b"\xfc\x11\x00" + i32c(0)),
        ("table.copy(2,0,2)+call", i32c(2) + i32c(0) + i32c(2) + b"\xfc\x0e\x00\x00" + i32c(2) + CALLT0),
        ("table.copy(3,0,2)", i32c(3) + i32c(0) + i32c(2) + b"\xfc\x0e\x00\x00" + i32c(0)),
        ("table.init(2,1,0,2)+call", i32c(2) + i32c(0) + i32c(2) + b"\xfc\x0c\x01\x00" + i32c(3) + CALLT0),
        ("table.init(2,1,1,2)", i32c(2) + i32c(1) + i32c(2) + b"\xfc\x0c\x01\x00" + i32c(0)),
        ("elem.drop+init", b"\xfc\x0d\x01" + i32c(2) + i32c(0) + i32c(1) + b"\xfc\x0c\x01\x00" + i32c(0)),
        ("elem.drop+init0", b"\xfc\x0d\x01" + i32c(2) + i32c(0) + i32c(0) + b"\xfc\x0c\x01\x00" + i32c(0)),
        ("init dropped active", i32c(2) + i32c(0) + i32c(1) + b"\xfc\x0c\x00\x00" + i32c(0))]:
    m, t0, t1, f0, f1 = table_module(4, 10)
    body_push = body_push.replace(CALLT0, b"\x11" + uleb(t0) + b"\x00")
    m.func([], [], [], ret_i32(m, body_push))
    m.exports.append(("main", 0, len(m.imports) + len(m.funcs) - 1))
    emit(label, m)

# ---- instantiation traps
m, *_ = table_module(1, 1)          # active elem segment of 2 into a table of 1
m.func([], [], [], b"")
m.exports.append(("main", 0, len(m.imports) + len(m.funcs) - 1))
emit("inst.elem-oob", m)
m = base_module()
m.datas.append(b"\x00" + i32c(MEM - 2) + b"\x0b" + vec([b"\x01"] * 3))
m.func([], [], [], b"")
m.exports.append(("main", 0, len(m.imports)))
emit("inst.data-oob", m)

# ---- br_table, start function, params/results, recursion
for k in [0, 1, 2, 3, 0xFFFFFFFF]:
    push = (b"\x02\x7f" + b"\x02\x7f" + b"\x02\x7f" + i32c(100) + i32c(k) + b"\x0e\x02\x00\x01\x02" +
            b"\x0b" + i32c(1) + b"\x6a" + b"\x0b" + i32c(10) + b"\x6a" + b"\x0b")
    simple(f"br_table({k:#x})", False, push)
m = base_module()
m.globals.append((I32, True, i32c(7) + b"\x0b"))
st = m.func([], [], [], i32c(35) + b"\x24\x00")
m.start = st
m.func([], [], [], ret_i32(m, b"\x23\x00"))
m.exports.append(("main", 0, len(m.imports) + 1))
emit("start-function", m)
m = base_module()
m.start = m.func([], [], [], b"\x00")
m.func([], [], [], b"")
m.exports.append(("main", 0, len(m.imports) + 1))
emit("start-traps", m)
m = base_module()
add3 = m.func([I32, I64, I32], [I64], [(2, I64)],
              b"\x20\x01" + b"\x20\x00\xac" + b"\x7c" + b"\x20\x02\xad" + b"\x7c")
m.func([], [], [], ret_i64(m, i32c(0xFFFFFFFF) + i64c(5) + i32c(0xFFFFFFFF) + b"\x10" + uleb(add3)))
m.exports.append(("main", 0, len(m.imports) + 1))
emit("params-results", m)

# ---- preparation outcomes (limits, features, imports, exports)
def prep(label, mutate):
    m = base_module()
    m.func([], [], [], b"")
    m.exports.append(("main", 0, len(m.imports)))
    mutate(m)
    emit(label, m)

prep("no-main", lambda m: m.exports.__setitem__(0, ("other", 0, len(m.imports))))
prep("main-is-memory", lambda m: m.exports.__setitem__(0, ("main", 2, 0)))
prep("main-bad-sig", lambda m: (m.funcs.__setitem__(0, (m.type([I32], []), [], b"")), None))
prep("unknown-import", lambda m: m.imports.append(("env", "no_such_fn", m.type([], []))) or
     m.exports.__setitem__(0, ("main", 0, 2)))
prep("import-bad-sig", lambda m: m.imports.append(("env", "panic", m.type([I32], []))) or
     m.exports.__setitem__(0, ("main", 0, 2)))
prep("import-other-module", lambda m: m.imports.append(("other", "panic", m.type([], []))) or
     m.exports.__setitem__(0, ("main", 0, 2)))
prep("too-many-tables", lambda m: m.tables.extend([(FUNCREF, 1, None), (FUNCREF, 1, None)]))
prep("too-many-elements", lambda m: m.tables.append((FUNCREF, 10001, None)))
prep("elements-ok", lambda m: m.tables.append((FUNCREF, 10000, None)))
prep("float-local(ood)", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [(1, F64)], b"")))
prep("too-many-locals-wp", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [(50001, I32)], b"")))
prep("params-65", lambda m: m.funcs.append((m.type([I32] * 65, []), [], b"")))
prep("params-64", lambda m: m.funcs.append((m.type([I32] * 64, []), [], b"")))
prep("blocks-5001", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], b"\x02\x40\x0b" * 5001)))
prep("blocks-5000", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], b"\x02\x40\x0b" * 5000)))
prep("opstack-8192", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], i64c(1) * 1024 + b"\x1a" * 1024)))
prep("opstack-8196", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], i64c(1) * 1024 + i32c(1) + b"\x1a" * 1025)))
prep("callind-opstack", lambda m: (m.tables.append((FUNCREF, 1, None)),
     m.funcs.__setitem__(0, (m.funcs[0][0], [], (i32c(0) + b"\x11" + uleb(m.type([], [])) + b"\x00") * 3000))))
prep("ref.func-undeclared", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], b"\xd2\x01\x1a")))
prep("memory.init-no-datacount", lambda m: m.datas.append(b"\x01" + vec([b"\x01"])) or
     m.funcs.__setitem__(0, (m.funcs[0][0], [], i32c(0) * 3 + b"\xfc\x08\x00\x00")))
prep("no-memory-load", lambda m: setattr(m, "memory", None) or
     m.funcs.__setitem__(0, (m.funcs[0][0], [], i32c(0) + b"\x28\x02\x00\x1a")))
prep("body-196609", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], b"\x01" * 196608)))
prep("simd-type(invalid)", lambda m: m.types.append(b"\x60\x01\x7b\x00"))
prep("multivalue", lambda m: m.types.append(functype([], [I32, I32])))

# ---- InstrumentedCodeTooLarge around the 16 MiB boundary (each `i32.load8_u` is its own gas point)
def big(nfuncs, reps):
    def mut(m):
        for _ in range(nfuncs):
            m.funcs.append((m.funcs[0][0], [], (i32c(0) + b"\x2d\x00\x00\x1a") * reps))
    return mut

for nf, reps in [(30, 12000), (37, 12000), (38, 11500), (38, 12000), (45, 12000)]:
    prep(f"instrumented-size({nf}x{reps})", big(nf, reps))

# ---- remaining NEAR limits (each just over and just at the limit)
def types(n):
    def mut(m):
        while len(m.types) < n:
            m.types.append(functype([I32] * len(m.types), []))
    return mut

def nfuncs(n):
    def mut(m):
        for _ in range(n - len(m.imports) - len(m.funcs)):
            m.funcs.append((m.funcs[0][0], [], b""))
    return mut

def locals_(nf, per):
    def mut(m):
        for _ in range(nf):
            m.funcs.append((m.funcs[0][0], [(per, I32)], b""))
    return mut

def params(nf):
    def mut(m):
        t = m.type([I32] * 64, [])
        for _ in range(nf):
            m.funcs.append((t, [], b""))
    return mut

def blocks(nf):
    def mut(m):
        for _ in range(nf):
            m.funcs.append((m.funcs[0][0], [], b"\x02\x40\x0b" * 5000))
    return mut

prep("types-1024", types(1024))
prep("types-1025", types(1025))
prep("functions-10000", nfuncs(10000))
prep("functions-10001", nfuncs(10001))
prep("locals-1000000", locals_(20, 50000))
prep("locals-1000001", lambda m: (locals_(20, 50000)(m), m.funcs.append((m.funcs[0][0], [(1, I32)], b""))))
prep("params-contract-50048", params(782))
prep("params-contract-49984", params(781))
prep("blocks-contract-50000", blocks(10))
prep("blocks-contract-55000", blocks(11))
for per, ty, np_ in [(49998, I32, 0), (49999, I32, 0), (49996, I32, 2), (49997, I32, 2), (24999, I64, 0)]:
    prep(f"wasmtime-locals({per},{ty:#x},{np_})",
         lambda m, per=per, ty=ty, np_=np_: m.funcs.append((m.type([I32] * np_, []), [(per, ty)], b"")))
prep("table-10000001", lambda m: m.tables.append((FUNCREF, 10000001, None)))
prep("export-name-100000", lambda m: m.exports.append(("x" * 100000, 0, len(m.imports))))
prep("export-name-99999", lambda m: m.exports.append(("x" * 99999, 0, len(m.imports))))
prep("memory-export-name-100000", lambda m: m.exports.append(("y" * 100000, 2, 0)))
prep("call_indirect-table-leb", lambda m: (m.tables.append((FUNCREF, 1, None)),
     m.funcs.__setitem__(0, (m.funcs[0][0], [], i32c(0) + b"\x11" + uleb(m.type([], [])) + b"\x80\x00"))))
prep("memory.fill-memidx-leb", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], i32c(0) * 3 + b"\xfc\x0b\x80\x00")))
prep("memory-export-name-100000", lambda m: m.exports.append(("y" * 100000, 2, 0)))
prep("memory.grow-memidx-leb", lambda m: m.funcs.__setitem__(0, (m.funcs[0][0], [], i32c(0) + b"\x40\x80\x00\x1a")))
prep("memory-import", lambda m: m.imports.append(("env", "memory", None)))

labels_path = sys.argv[1] if len(sys.argv) > 1 else None
for lab, gas, hx in cases:
    print(gas, hx)
if labels_path:
    with open(labels_path, "w") as f:
        for lab, _, _ in cases:
            f.write(lab + "\n")
print(f"{len(cases)} cases", file=sys.stderr)
