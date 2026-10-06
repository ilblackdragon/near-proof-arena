#!/usr/bin/env python3
"""Clean-room NEAR PV86 WASM contract execution (D3-alpha integer subset).

Written from docs/research/near-wasm-prose-spec.md, docs/research/near-wasm-boundary.md (Appendix A)
and the WebAssembly 2.0 specification only; ambiguities were resolved by black-box runs of the nearcore
harness (see README.md).  Standard library only.

  nearwasm.py [--charge-points] < cases

Input lines: `<prepaid_gas> <wasm_hex> [<receiver>,...]`.
Output: one outcome line per input line (`ok <burnt> <used> <ret|-> <balance>` / `abort <burnt> <used> <err>`),
or with --charge-points, one line of per-function charge points.
"""
import mmap
import struct
import sys

# ----------------------------------------------------------------------------------------------
# Parameters (PV86)
R = 822_756                  # regular op cost
LB = 26_328_192              # linear op base
LU = 822_756                 # linear op unit
STACK_BUDGET = 262_144
MAX_GAS_BURNT = 10 ** 15
U64 = (1 << 64) - 1
LOAD_BYTES = 1_089_295
LOAD_BASE = 35_445_963
PAGE = 65536
MEM_INIT_PAGES = 1024
MEM_MAX_PAGES = 2048
TABLE_CAP = 10_000
BALANCE = 10 ** 24
CURRENT_ACCOUNT = b"alice.near"

# ExtCosts (gas)
C_BASE = 264_768_111
C_READ_MEM_BASE = 2_609_863_200
C_READ_MEM_BYTE = 3_801_333
C_UTF8_BASE = 3_111_779_061
C_UTF8_BYTE = 291_580_479
# action fees: (send_sir, send_not_sir, exec)
F_NEW_ACTION_RECEIPT = (108_059_500_000, 108_059_500_000, 108_059_500_000)
F_DATA_RECEIPT_BYTE = (17_212_011, 47_683_715, 17_212_011)
F_FUNCTION_CALL = (200_000_000_000, 200_000_000_000, 780_000_000_000)
F_FUNCTION_CALL_BYTE = (2_235_934, 47_683_715, 2_235_934)
MAX_RETURNED_DATA = 4 * 1024 * 1024
MAX_PROMISES = 1024

# NEAR preparation limits
MAX_TYPES = 1024
MAX_FUNCTIONS = 10_000
MAX_TABLES = 1
MAX_TABLE_ELEMS = 10_000
MAX_BODY_SIZE = 196_608
MAX_LOCALS_CONTRACT = 1_000_000
MAX_PARAMS_FN = 64
MAX_PARAMS_CONTRACT = 50_000
MAX_OPSTACK = 8_192
MAX_BLOCKS_FN = 5_000
MAX_BLOCKS_CONTRACT = 50_000
MAX_INSTRUMENTED = 16 * 1024 * 1024
ENGINE_LOCALS = 50_000 - 2

# wasmparser implementation limits (prose spec §1)
WP_MAX_LOCALS = 50_000
WP_MAX_NAME = 100_000
WP_MAX_PARAMS = 1_000
WP_MAX_RESULTS = 1_000
WP_MAX_BR_TABLE = 131_072

I32, I64, F32, F64, V128, FUNCREF, EXTERNREF = 0x7F, 0x7E, 0x7D, 0x7C, 0x7B, 0x70, 0x6F
VSIZE = {I32: 4, I64: 8, FUNCREF: 8, F32: 4, F64: 8}
TNAME = {I32: "i32", I64: "i64", F32: "f32", F64: "f64", FUNCREF: "funcref"}


class PrepError(Exception):
    pass


class OutOfDomain(Exception):
    pass


class Unmodeled(Exception):
    pass


class Trap(Exception):
    pass


class HostErr(Exception):
    pass


def deser():
    return PrepError("Deserialization")


# ----------------------------------------------------------------------------------------------
# Binary reader

class Reader:
    __slots__ = ("b", "p", "end")

    def __init__(self, b, p=0, end=None):
        self.b, self.p = b, p
        self.end = len(b) if end is None else end

    def eof(self):
        return self.p >= self.end

    def u8(self):
        if self.p >= self.end:
            raise deser()
        v = self.b[self.p]
        self.p += 1
        return v

    def bytes(self, n):
        if n > self.end - self.p:
            raise deser()
        v = self.b[self.p:self.p + n]
        self.p += n
        return v

    def uleb(self, bits):
        result = shift = 0
        maxlen = (bits + 6) // 7
        for i in range(maxlen):
            byte = self.u8()
            result |= (byte & 0x7F) << shift
            if not byte & 0x80:
                if i == maxlen - 1:
                    used = bits - 7 * i
                    if byte >> used:
                        raise deser()
                return result
            shift += 7
        raise deser()

    def sleb(self, bits):
        result = shift = 0
        maxlen = (bits + 6) // 7
        for i in range(maxlen):
            byte = self.u8()
            result |= (byte & 0x7F) << shift
            shift += 7
            if not byte & 0x80:
                if i == maxlen - 1:
                    used = bits - 7 * i          # value bits in this byte (incl. sign bit)
                    rest = byte & 0x7F
                    sign = (rest >> (used - 1)) & 1
                    hi = rest >> used
                    if hi != (((1 << (7 - used)) - 1) if sign else 0):
                        raise deser()
                if byte & 0x40:
                    result -= 1 << shift
                return result
        raise deser()

    def u32(self):
        return self.uleb(32)

    def name(self):
        n = self.u32()
        if n > WP_MAX_NAME:
            raise deser()
        raw = self.bytes(n)
        try:
            return raw.decode("utf-8")
        except UnicodeDecodeError:
            raise deser()


# ----------------------------------------------------------------------------------------------
# Module structures

class Func:
    __slots__ = ("idx", "typeidx", "params", "results", "locals", "ops", "body_start", "code", "frame",
                 "opmax", "nblocks", "points", "imported", "imp_name", "targeted", "live")


class Module:
    pass


FLOAT_SEEN = [False]


def read_valtype(r, allow_ref=True):
    t = r.u8()
    if t in (I32, I64):
        return t
    if t in (F32, F64):
        FLOAT_SEEN[0] = True
        return t
    if t == FUNCREF and allow_ref:
        return t
    raise deser()


ABSTRACT_HEAP = {0x70, 0x6F, 0x6E, 0x71, 0x72, 0x73, 0x6D, 0x6B, 0x6A, 0x6C, 0x69, 0x74}


def parse_valtype_syntax(r):
    """Value-type *syntax* (as accepted by a parser that knows every proposal's encodings); returns the type
    byte for the valid D3 types and a marker for anything else that parses.  Invalid syntax -> Deserialization."""
    t = r.b[r.p] if r.p < r.end else None
    if t is None:
        raise deser()
    if t in (I32, I64, F32, F64, V128):
        r.p += 1
        return t
    if t in (0x63, 0x64):
        r.p += 1
        ht = r.sleb(33)
        if ht < 0 and (ht & 0x7F) not in ABSTRACT_HEAP:
            raise deser()
        return ("ref", t, ht)
    ht = r.sleb(33)
    if ht < 0:
        if (ht & 0x7F) not in ABSTRACT_HEAP:
            raise deser()
        return ht & 0x7F       # FUNCREF is valid; other abstract shorthands are rejected by validation
    return ("ref", "concrete", ht)


def read_reftype(r):
    t = r.u8()
    if t != FUNCREF:
        raise deser()
    return t


def read_limits(r, maxbound):
    flag = r.u8()
    if flag == 0:
        mn = r.u32()
        mx = None
    elif flag == 1:
        mn = r.u32()
        mx = r.u32()
    else:
        raise deser()
    if mn > maxbound or (mx is not None and (mx > maxbound or mn > mx)):
        raise deser()
    return mn, mx


# ----------------------------------------------------------------------------------------------
# Decoding + validation + NEAR preparation checks

SEC_ORDER = {1: 1, 2: 2, 3: 3, 4: 4, 5: 5, 6: 6, 7: 7, 8: 8, 9: 9, 12: 10, 10: 11, 11: 12}


def const_expr(r, m, want):
    """Constant expression; returns ('i', value) | ('ref', funcidx|None)."""
    op = r.u8()
    if op == 0x41:
        v, t = r.sleb(32) & 0xFFFFFFFF, I32
        res = ("i", v)
    elif op == 0x42:
        v, t = r.sleb(64) & U64, I64
        res = ("i", v)
    elif op in (0x43, 0x44):
        r.bytes(4 if op == 0x43 else 8)
        FLOAT_SEEN[0] = True
        t = F32 if op == 0x43 else F64
        res = ("f", None)
    elif op == 0xD0:
        t = read_heaptype(r)
        res = ("ref", None)
    elif op == 0xD2:
        f = r.u32()
        if f >= m.nfuncs_total:
            raise deser()
        m.declared.add(f)
        t = FUNCREF
        res = ("ref", f)
    elif op == 0x23:
        # global.get: only imported globals are allowed (WebAssembly 2.0); NEAR rejects global imports.
        r.u32()
        raise deser()
    else:
        raise deser()
    if r.u8() != 0x0B:
        raise deser()
    if t != want:
        raise deser()
    return res


def read_heaptype(r):
    t = r.u8()
    if t == FUNCREF:
        return FUNCREF
    raise deser()


def decode(b):
    FLOAT_SEEN[0] = False
    m = Module()
    m.types = []
    m.imports = []
    m.funcs = []          # all functions (imports first)
    m.tables = []
    m.has_memory = False
    m.globals = []
    m.exports = {}
    m.start = None
    m.elems = []
    m.datacount = None
    m.datas = []
    m.declared = set()
    m.nfuncs_total = 0
    m.ftypes = []
    m.serialization_error = False
    r = Reader(b)
    if r.bytes(4) != b"\x00asm" or r.bytes(4) != b"\x01\x00\x00\x00":
        raise deser()
    last = 0
    fsec_types = []
    code_seen = False
    locals_total = 0
    while not r.eof():
        sid = r.u8()
        size = r.u32()
        if size > r.end - r.p:
            raise deser()
        s = Reader(b, r.p, r.p + size)
        r.p += size
        if sid == 0:
            s.name()
            continue
        if sid not in SEC_ORDER:
            raise deser()
        if SEC_ORDER[sid] <= last:
            raise deser()
        last = SEC_ORDER[sid]
        if sid == 1:
            n = s.u32()
            if n > MAX_TYPES:
                raise PrepError("TooManyTypes")
            for _ in range(n):
                if s.u8() != 0x60:
                    raise deser()
                np_ = s.u32()
                if np_ > WP_MAX_PARAMS:
                    raise deser()
                ps = tuple(read_valtype(s) for _ in range(np_))
                nr = s.u32()
                if nr > WP_MAX_RESULTS:
                    raise deser()
                rs = tuple(read_valtype(s) for _ in range(nr))
                if nr > 1:
                    raise deser()
                m.types.append((ps, rs))
        elif sid == 2:
            n = s.u32()
            imps = []
            for _ in range(n):
                mod = s.name()
                nm = s.name()
                kind = s.u8()
                if kind == 0:
                    t = s.u32()
                    if t >= len(m.types):
                        raise deser()
                    imps.append((mod, nm, 0, t))
                elif kind == 1:
                    read_reftype(s)
                    read_limits(s, 0xFFFFFFFF)
                    imps.append((mod, nm, 1, None))
                elif kind == 2:
                    read_limits(s, 65536)
                    imps.append((mod, nm, 2, None))
                elif kind == 3:
                    read_valtype(s)
                    mu = s.u8()
                    if mu > 1:
                        raise deser()
                    imps.append((mod, nm, 3, None))
                else:
                    raise deser()
            if not s.eof():
                raise deser()
            nfi = 0
            for mod, nm, kind, t in imps:
                if mod != "env":
                    raise PrepError("Instantiate")
                if kind in (1, 3):
                    raise PrepError("Instantiate")
                if kind == 2:
                    raise PrepError("Memory")
                nfi += 1
                if nfi > MAX_FUNCTIONS:
                    raise PrepError("TooManyFunctions")
            for mod, nm, kind, t in imps:
                f = Func()
                f.idx = len(m.funcs)
                f.typeidx = t
                f.params, f.results = m.types[t]
                f.imported = True
                f.imp_name = nm
                m.funcs.append(f)
                m.imports.append((nm, t))
            m.nfuncs_total = len(m.funcs)
            m.ftypes = [f.typeidx for f in m.funcs]
        elif sid == 3:
            n = s.u32()
            for _ in range(n):
                t = s.u32()
                if t >= len(m.types):
                    raise deser()
                fsec_types.append(t)
            m.nfuncs_total = len(m.funcs) + len(fsec_types)
            m.ftypes = [f.typeidx for f in m.funcs] + fsec_types
        elif sid == 4:
            n = s.u32()
            for _ in range(n):
                read_reftype(s)
                mn, mx = read_limits(s, 0xFFFFFFFF)
                m.tables.append((mn, mx))
            if len(m.tables) > MAX_TABLES:
                raise PrepError("TooManyTables")
            for mn, mx in m.tables:
                if mn > MAX_TABLE_ELEMS:
                    raise PrepError("TooManyTableElements")
        elif sid == 5:
            n = s.u32()
            for _ in range(n):
                read_limits(s, 65536)
            if n > 1:
                raise deser()
            m.has_memory = n == 1
        elif sid == 6:
            n = s.u32()
            for _ in range(n):
                t = read_valtype(s)
                mu = s.u8()
                if mu > 1:
                    raise deser()
                init = const_expr(s, m, t)
                m.globals.append([t, mu == 1, init[1] if init[0] == "i" else init[1]])
        elif sid == 7:
            n = s.u32()
            for _ in range(n):
                nm = s.name()
                kind = s.u8()
                idx = s.u32()
                if kind == 0:
                    if idx >= m.nfuncs_total:
                        raise deser()
                    m.declared.add(idx)
                elif kind == 1:
                    if idx >= len(m.tables):
                        raise deser()
                elif kind == 2:
                    if idx >= (1 if m.has_memory else 0):
                        raise deser()
                elif kind == 3:
                    if idx >= len(m.globals):
                        raise deser()
                else:
                    raise deser()
                if nm in m.exports:
                    raise deser()
                m.exports[nm] = (kind, idx)
                if kind != 2 and len(nm.encode()) >= WP_MAX_NAME:
                    # NEAR renames the export to "\0" + name; the instrumentation's re-parse then rejects it
                    m.serialization_error = True
        elif sid == 8:
            f = s.u32()
            if f >= m.nfuncs_total:
                raise deser()
            t = m.funcs[f].typeidx if f < len(m.funcs) else fsec_types[f - len(m.funcs)]
            if m.types[t] != ((), ()):
                raise deser()
            m.start = f
        elif sid == 9:
            n = s.u32()
            for _ in range(n):
                flags = s.u32()
                if flags > 7:
                    raise deser()
                mode = "passive"
                table = 0
                offset = None
                if flags & 1 == 0:
                    mode = "active"
                    if flags & 2:
                        table = s.u32()
                    offset = const_expr(s, m, I32)[1]
                    if table >= len(m.tables):
                        raise deser()
                elif flags & 2:
                    mode = "declarative"
                items = []
                if flags & 4:
                    if flags & 3:
                        read_reftype(s)
                    k = s.u32()
                    for _ in range(k):
                        items.append(const_expr(s, m, FUNCREF)[1])
                else:
                    if flags & 3:
                        if s.u8() != 0x00:
                            raise deser()
                    k = s.u32()
                    for _ in range(k):
                        f = s.u32()
                        if f >= m.nfuncs_total:
                            raise deser()
                        m.declared.add(f)
                        items.append(f)
                m.elems.append((mode, table, offset, items))
        elif sid == 12:
            m.datacount = s.u32()
        elif sid == 10:
            code_seen = True
            n = s.u32()
            if len(m.funcs) + n > MAX_FUNCTIONS:
                raise PrepError("TooManyFunctions")
            if n != len(fsec_types):
                raise deser()
            for k in range(n):
                bsize = s.u32()
                if bsize > s.end - s.p:
                    raise deser()
                if bsize > MAX_BODY_SIZE:
                    raise PrepError("FunctionBodyTooLarge")
                br = Reader(b, s.p, s.p + bsize)
                s.p += bsize
                f = Func()
                f.idx = len(m.funcs)
                f.typeidx = fsec_types[k]
                f.params, f.results = m.types[f.typeidx]
                f.imported = False
                f.imp_name = None
                # NEAR sums declared locals group by group while *parsing* them; the per-function limit and
                # the validity of each local type are checked afterwards by the validator.
                nd = br.u32()
                locs = []
                total = 0
                for _ in range(nd):
                    c = br.u32()
                    t = parse_valtype_syntax(br)
                    total += c
                    locals_total += c
                    if locals_total > MAX_LOCALS_CONTRACT:
                        raise PrepError("TooManyLocals")
                    locs.append((c, t))
                for c, t in locs:
                    if t not in (I32, I64, F32, F64, FUNCREF):
                        raise deser()
                    if t in (F32, F64):
                        FLOAT_SEEN[0] = True
                if total + len(f.params) > WP_MAX_LOCALS:
                    raise deser()
                f.locals = []
                for c, t in locs:
                    f.locals.extend([t] * c)
                f.body_start = br.p
                validate_body(m, f, br)
                m.funcs.append(f)
        elif sid == 11:
            n = s.u32()
            if m.datacount is not None and n != m.datacount:
                raise deser()
            for _ in range(n):
                flags = s.u32()
                if flags == 0:
                    if not m.has_memory:
                        raise deser()
                    off = const_expr(s, m, I32)[1]
                    mode = "active"
                elif flags == 1:
                    off, mode = None, "passive"
                elif flags == 2:
                    mi = s.u32()
                    if mi != 0 or not m.has_memory:
                        raise deser()
                    off = const_expr(s, m, I32)[1]
                    mode = "active"
                else:
                    raise deser()
                k = s.u32()
                data = s.bytes(k)
                m.datas.append((mode, off, data))
        if not s.eof():
            raise deser()
    if fsec_types and not code_seen:
        raise deser()
    if m.datacount is not None and m.datacount != len(m.datas):
        raise deser()
    m.has_float = FLOAT_SEEN[0]
    return m


# ---------------------------------------------------------------------------- function bodies

EFFECT = set(range(0x28, 0x3F)) | {0x6D, 0x6E, 0x6F, 0x70, 0x7F, 0x80, 0x81, 0x82,
                                   0x10, 0x11, 0x25, 0x26, 0x04, 0x0C, 0x0D, 0x0E, 0x0F, 0x00}
BULK = {0x40, 0xFC08, 0xFC0A, 0xFC0B, 0xFC0C, 0xFC0E, 0xFC0F, 0xFC11}

# numeric op typing: opcode -> (pops, push)
NUMTYPES = {}
for _o in range(0x46, 0x50):
    NUMTYPES[_o] = ((I32, I32), I32)
for _o in range(0x51, 0x5B):
    NUMTYPES[_o] = ((I64, I64), I32)
for _o in range(0x6A, 0x79):
    NUMTYPES[_o] = ((I32, I32), I32)
for _o in range(0x7C, 0x8B):
    NUMTYPES[_o] = ((I64, I64), I64)
for _o in (0x67, 0x68, 0x69, 0xC0, 0xC1):
    NUMTYPES[_o] = ((I32,), I32)
for _o in (0x79, 0x7A, 0x7B, 0xC2, 0xC3, 0xC4):
    NUMTYPES[_o] = ((I64,), I64)
NUMTYPES[0x45] = ((I32,), I32)
NUMTYPES[0x50] = ((I64,), I32)
NUMTYPES[0xA7] = ((I64,), I32)
NUMTYPES[0xAC] = ((I32,), I64)
NUMTYPES[0xAD] = ((I32,), I64)
# float operators: validated (typing only), never executed
FLOATTYPES = {}
for _o in range(0x5B, 0x61):
    FLOATTYPES[_o] = ((F32, F32), I32)
for _o in range(0x61, 0x67):
    FLOATTYPES[_o] = ((F64, F64), I32)
for _o in range(0x8B, 0x92):
    FLOATTYPES[_o] = ((F32,), F32)
for _o in range(0x92, 0x99):
    FLOATTYPES[_o] = ((F32, F32), F32)
for _o in range(0x99, 0xA0):
    FLOATTYPES[_o] = ((F64,), F64)
for _o in range(0xA0, 0xA7):
    FLOATTYPES[_o] = ((F64, F64), F64)
for _o, _a, _b in [(0xA8, F32, I32), (0xA9, F32, I32), (0xAA, F64, I32), (0xAB, F64, I32),
                   (0xAE, F32, I64), (0xAF, F32, I64), (0xB0, F64, I64), (0xB1, F64, I64),
                   (0xB2, I32, F32), (0xB3, I32, F32), (0xB4, I64, F32), (0xB5, I64, F32), (0xB6, F64, F32),
                   (0xB7, I32, F64), (0xB8, I32, F64), (0xB9, I64, F64), (0xBA, I64, F64), (0xBB, F32, F64),
                   (0xBC, F32, I32), (0xBD, F64, I64), (0xBE, I32, F32), (0xBF, I64, F64),
                   (0xFC00, F32, I32), (0xFC01, F32, I32), (0xFC02, F64, I32), (0xFC03, F64, I32),
                   (0xFC04, F32, I64), (0xFC05, F32, I64), (0xFC06, F64, I64), (0xFC07, F64, I64)]:
    FLOATTYPES[_o] = ((_a,), _b)
FLOAT_LOADS = {0x2A: (2, F32), 0x2B: (3, F64)}
FLOAT_STORES = {0x38: (2, F32), 0x39: (3, F64)}
# loads: op -> (natural align log2, result type, size, signed)
LOADS = {0x28: (2, I32, 4, False), 0x29: (3, I64, 8, False), 0x2C: (0, I32, 1, True), 0x2D: (0, I32, 1, False),
         0x2E: (1, I32, 2, True), 0x2F: (1, I32, 2, False), 0x30: (0, I64, 1, True), 0x31: (0, I64, 1, False),
         0x32: (1, I64, 2, True), 0x33: (1, I64, 2, False), 0x34: (2, I64, 4, True), 0x35: (2, I64, 4, False)}
STORES = {0x36: (2, I32, 4), 0x37: (3, I64, 8), 0x3A: (0, I32, 1), 0x3B: (1, I32, 2), 0x3C: (0, I64, 1),
          0x3D: (1, I64, 2), 0x3E: (2, I64, 4)}


class Ctrl:
    __slots__ = ("kind", "label", "end", "height", "unreach", "pc", "else_pc", "end_pc")

    def __init__(self, kind, label, end, height, pc):
        self.kind, self.label, self.end, self.height, self.pc = kind, label, end, height, pc
        self.unreach = False
        self.else_pc = None
        self.end_pc = None


def read_blocktype(r, m):
    """Block types: only the single bytes 0x40 / i32 / i64 / f32 / f64 / funcref are accepted.  Type-index block
    types (multi-value) and non-canonical multi-byte s33 encodings are rejected (resolved by nearcore)."""
    b = r.u8()
    if b == 0x40:
        return ()
    if b in (I32, I64, FUNCREF):
        return (b,)
    if b in (F32, F64):
        FLOAT_SEEN[0] = True
        return (b,)
    raise deser()


def validate_body(m, f, r):
    """Decode and validate one body.  Records f.ops: list of [key, imm, info] where info carries
    control structure / branch heights for compilation."""
    vals = []
    ctrls = []
    ops = []
    locals_t = list(f.params) + f.locals
    nmem = 1 if m.has_memory else 0
    ntab = len(m.tables)

    def push(t):
        vals.append(t)

    def pop(expect=None):
        c = ctrls[-1]
        if len(vals) == c.height:
            if c.unreach:
                return None
            raise deser()
        t = vals.pop()
        if expect is not None and t is not None and t != expect:
            raise deser()
        return t

    def pops(ts):
        for t in reversed(ts):
            pop(t)

    def unreachable():
        c = ctrls[-1]
        del vals[c.height:]
        c.unreach = True

    def label_types(c):
        return () if c.kind == "loop" else c.end

    def label(d):
        if d >= len(ctrls):
            raise deser()
        return ctrls[-1 - d]

    ctrls.append(Ctrl("func", f.results, f.results, 0, -1))
    while True:
        if not ctrls:
            if not r.eof():
                raise deser()
            break
        pc = len(ops)
        op = r.u8()
        imm = None
        info = None
        if op == 0xFC:
            op = 0xFC00 | r.u32()
            if op > 0xFCFF:
                raise deser()
        if op in NUMTYPES:
            ps, res = NUMTYPES[op]
            pops(ps)
            push(res)
        elif op in FLOATTYPES:
            FLOAT_SEEN[0] = True
            ps, res = FLOATTYPES[op]
            pops(ps)
            push(res)
        elif op == 0x43 or op == 0x44:
            FLOAT_SEEN[0] = True
            r.bytes(4 if op == 0x43 else 8)
            push(F32 if op == 0x43 else F64)
        elif op in FLOAT_LOADS or op in FLOAT_STORES:
            FLOAT_SEEN[0] = True
            al, t = FLOAT_LOADS[op] if op in FLOAT_LOADS else FLOAT_STORES[op]
            a = r.u32()
            if a & 0x40:
                raise deser()
            r.u32()
            if a > al or not nmem:
                raise deser()
            if op in FLOAT_LOADS:
                pop(I32)
                push(t)
            else:
                pop(t)
                pop(I32)
        elif op == 0x20 or op == 0x21 or op == 0x22:
            imm = r.u32()
            if imm >= len(locals_t):
                raise deser()
            t = locals_t[imm]
            if op == 0x20:
                push(t)
            elif op == 0x21:
                pop(t)
            else:
                pop(t)
                push(t)
        elif op == 0x41:
            imm = r.sleb(32) & 0xFFFFFFFF
            push(I32)
        elif op == 0x42:
            imm = r.sleb(64) & U64
            push(I64)
        elif op in LOADS or op in STORES:
            if op in LOADS:
                al, t, size, sg = LOADS[op]
            else:
                al, t, size = STORES[op]
            a = r.u32()
            if a & 0x40:
                raise deser()
            off = r.u32()
            if a > al:
                raise deser()
            if not nmem:
                raise deser()
            imm = off
            if op in LOADS:
                pop(I32)
                push(t)
            else:
                pop(t)
                pop(I32)
        elif op == 0x02 or op == 0x03:
            bt = read_blocktype(r, m)
            ctrls.append(Ctrl("block" if op == 0x02 else "loop", bt, bt, len(vals), pc))
            info = ctrls[-1]
        elif op == 0x04:
            bt = read_blocktype(r, m)
            pop(I32)
            ctrls.append(Ctrl("if", bt, bt, len(vals), pc))
            info = ctrls[-1]
        elif op == 0x05:
            c = ctrls[-1]
            if c.kind != "if" or c.else_pc is not None:
                raise deser()
            pops(c.end)
            if len(vals) != c.height:
                raise deser()
            c.else_pc = pc
            c.unreach = False
            info = c
        elif op == 0x0B:
            c = ctrls[-1]
            pops(c.end)
            if len(vals) != c.height:
                raise deser()
            if c.kind == "if" and c.else_pc is None and c.end:
                raise deser()
            ctrls.pop()
            c.end_pc = pc
            for t in c.end:
                push(t)
            info = c
        elif op == 0x0C:
            d = r.u32()
            c = label(d)
            lt = label_types(c)
            pops(lt)
            info = (c, len(lt))
            unreachable()
        elif op == 0x0D:
            d = r.u32()
            pop(I32)
            c = label(d)
            lt = label_types(c)
            pops(lt)
            for t in lt:
                push(t)
            info = (c, len(lt))
        elif op == 0x0E:
            n = r.u32()
            if n > WP_MAX_BR_TABLE:
                raise deser()
            ds = [r.u32() for _ in range(n)]
            dd = r.u32()
            pop(I32)
            cd = label(dd)
            arity = len(label_types(cd))
            tl = []
            for d in ds:
                c = label(d)
                lt = label_types(c)
                if len(lt) != arity:
                    raise deser()
                # check operand compatibility (push back)
                popped = []
                for t in reversed(lt):
                    popped.append(pop(t))
                for t in reversed(popped):
                    vals.append(t)
                tl.append(c)
            pops(label_types(cd))
            info = (tl, cd, arity)
            unreachable()
        elif op == 0x0F:
            pops(f.results)
            info = len(f.results)
            unreachable()
        elif op == 0x10:
            fi = r.u32()
            if fi >= m.nfuncs_total:
                raise deser()
            ps, rs = func_type(m, fi)
            pops(ps)
            for t in rs:
                push(t)
            imm = fi
        elif op == 0x11:
            ti = r.u32()
            tb = r.u32()
            if ti >= len(m.types) or tb >= ntab:
                raise deser()
            pop(I32)
            ps, rs = m.types[ti]
            pops(ps)
            for t in rs:
                push(t)
            imm = (ti, tb)
        elif op == 0x1A:
            t = pop()
            imm = VSIZE.get(t, 4)
        elif op == 0x1B:
            pop(I32)
            t1 = pop()
            t2 = pop()
            if t1 == FUNCREF or t2 == FUNCREF:
                raise deser()
            if t1 is not None and t2 is not None and t1 != t2:
                raise deser()
            push(t1 if t1 is not None else t2)
            imm = VSIZE.get(t1 if t1 is not None else t2, 4)
        elif op == 0x1C:
            n = r.u32()
            if n != 1:
                raise deser()
            t = read_valtype(r)
            pop(I32)
            pop(t)
            pop(t)
            push(t)
            imm = VSIZE[t]
        elif op == 0x23 or op == 0x24:
            imm = r.u32()
            if imm >= len(m.globals):
                raise deser()
            t, mu, _ = m.globals[imm]
            if op == 0x23:
                push(t)
            else:
                if not mu:
                    raise deser()
                pop(t)
        elif op == 0x3F or op == 0x40:
            if r.u8() != 0x00:
                raise deser()
            if not nmem:
                raise deser()
            if op == 0x40:
                pop(I32)
            push(I32)
        elif op == 0x00 or op == 0x01:
            if op == 0x00:
                unreachable()
        elif op == 0x25 or op == 0x26:
            imm = r.u32()
            if imm >= ntab:
                raise deser()
            if op == 0x25:
                pop(I32)
                push(FUNCREF)
            else:
                pop(FUNCREF)
                pop(I32)
        elif op == 0xD0:
            read_heaptype(r)
            push(FUNCREF)
        elif op == 0xD1:
            t = pop()
            if t is not None and t != FUNCREF:
                raise deser()
            push(I32)
        elif op == 0xD2:
            imm = r.u32()
            if imm >= m.nfuncs_total or imm not in m.declared:
                raise deser()
            push(FUNCREF)
        elif op == 0xFC08:
            imm = r.u32()
            if m.datacount is None:
                raise deser()
            if r.u32() != 0:
                raise deser()
            if not nmem or imm >= m.datacount:
                raise deser()
            pops((I32, I32, I32))
        elif op == 0xFC09:
            imm = r.u32()
            if m.datacount is None or imm >= m.datacount:
                raise deser()
        elif op == 0xFC0A:
            if r.u32() != 0 or r.u32() != 0:
                raise deser()
            if not nmem:
                raise deser()
            pops((I32, I32, I32))
        elif op == 0xFC0B:
            if r.u32() != 0:
                raise deser()
            if not nmem:
                raise deser()
            pops((I32, I32, I32))
        elif op == 0xFC0C:
            e = r.u32()
            t = r.u32()
            if t >= ntab or e >= len(m.elems):
                raise deser()
            pops((I32, I32, I32))
            imm = (e, t)
        elif op == 0xFC0D:
            imm = r.u32()
            if imm >= len(m.elems):
                raise deser()
        elif op == 0xFC0E:
            d = r.u32()
            sx = r.u32()
            if d >= ntab or sx >= ntab:
                raise deser()
            pops((I32, I32, I32))
            imm = (d, sx)
        elif op in (0xFC0F, 0xFC10, 0xFC11):
            imm = r.u32()
            if imm >= ntab:
                raise deser()
            if op == 0xFC0F:
                pop(I32)
                pop(FUNCREF)
                push(I32)
            elif op == 0xFC10:
                push(I32)
            else:
                pops((I32, FUNCREF, I32))
        else:
            raise deser()
        ops.append([op, imm, info, len(vals)])
    f.ops = ops


def func_type(m, fi):
    return m.types[m.ftypes[fi]]


# ---------------------------------------------------------------------------- static analyses

def analyse(m, f):
    """Liveness, branch targets, block count, operand-stack max, charge points."""
    ops = f.ops
    n = len(ops)
    # branch targets (live or dead); keyed by the opening pc of block/loop
    targeted = set()
    stack = [-1]  # opening pcs; -1 = function body
    nblocks = 0
    for pc, (op, imm, info, _) in enumerate(ops):
        if op in (0x02, 0x03, 0x04):
            stack.append(pc)
            nblocks += 1
        elif op == 0x0B:
            stack.pop()
        elif op in (0x0C, 0x0D):
            targeted.add(info[0].pc)
        elif op == 0x0E:
            for c in info[0]:
                targeted.add(c.pc)
            targeted.add(info[1].pc)
    f.nblocks = nblocks
    # liveness: frames [opening_live, dead]
    live = [False] * n
    frames = [[True, False]]
    for pc, (op, imm, info, _) in enumerate(ops):
        top = frames[-1]
        if op in (0x05, 0x0B):
            live[pc] = top[0]
            if op == 0x05:
                top[1] = False
            else:
                frames.pop()
            continue
        cur = top[0] and not top[1]
        live[pc] = cur
        if op in (0x02, 0x03, 0x04):
            frames.append([cur, False])
        elif op in (0x0C, 0x0E, 0x0F, 0x00):
            top[1] = True
    f.opmax = opstack_max(m, f, live)
    # charge points
    points = []   # (pc, c, l)
    cur_start = None
    cur_fee = 0

    def close():
        nonlocal cur_start, cur_fee
        if cur_start is not None and cur_fee:
            points.append([cur_start, cur_fee, 0])
        cur_start = None
        cur_fee = 0

    boundary_next = True
    pending_loop_fee = 0
    prev_live = True
    for pc, (op, imm, info, _) in enumerate(ops):
        if not live[pc]:
            prev_live = False
            continue
        if not prev_live:
            boundary_next = True
        prev_live = True
        if op in BULK:
            close()
            if pending_loop_fee:
                points.append([pc, pending_loop_fee + LB, LU])
                pending_loop_fee = 0
            else:
                points.append([pc, LB, LU])
            boundary_next = True
            continue
        if boundary_next:
            close()
            cur_start = pc
            boundary_next = False
        if pending_loop_fee:
            cur_fee += pending_loop_fee
            pending_loop_fee = 0
        if op == 0x03 and pc in targeted:
            # loop ends the preceding range; its fee is paid at the start of the body
            boundary_next = True
            pending_loop_fee = R
            continue
        if op in (0x02, 0x05, 0x0B):
            fee = 0
        else:
            fee = R
        cur_fee += fee
        if op in EFFECT:
            boundary_next = True
        elif op == 0x05:
            boundary_next = True
        elif op == 0x0B:
            c = info
            if c.kind == "if" or (c.kind == "block" and c.pc in targeted):
                boundary_next = True
    close()
    # merge same-pc points (may arise for a loop whose body starts with a bulk op; handled above)
    f.points = points
    f.targeted = targeted
    f.live = live


def opstack_max(m, f, live):
    ops = f.ops
    h = 0
    mx = 0
    entries = []   # (entry height, result bytes)
    for pc, (op, imm, info, _) in enumerate(ops):
        if op in (0x02, 0x03):
            entries.append((h, sum(VSIZE[t] for t in info.end)))
            continue
        if op == 0x04:
            if live[pc]:
                h -= 4
            entries.append((h, sum(VSIZE[t] for t in info.end)))
            continue
        if op == 0x05:
            h = entries[-1][0]
            continue
        if op == 0x0B:
            if entries:
                eh, rb = entries.pop()
                h = eh + rb
            else:
                h = sum(VSIZE[t] for t in f.results)
            if h > mx:
                mx = h
            continue
        if not live[pc]:
            continue
        pop_b, push_b = stack_effect(m, f, op, imm, info, ops[pc])
        h -= pop_b
        h += push_b
        if h > mx:
            mx = h
    return mx


def stack_effect(m, f, op, imm, info, rec):
    """(bytes popped, bytes pushed) for live operators."""
    if op in NUMTYPES:
        ps, res = NUMTYPES[op]
        return sum(VSIZE[t] for t in ps), VSIZE[res]
    if op == 0x20:
        return 0, VSIZE[local_type(f, imm)]
    if op == 0x21:
        return VSIZE[local_type(f, imm)], 0
    if op == 0x22:
        s = VSIZE[local_type(f, imm)]
        return s, s
    if op == 0x41:
        return 0, 4
    if op == 0x42:
        return 0, 8
    if op in LOADS:
        return 4, VSIZE[LOADS[op][1]]
    if op in STORES:
        return 4 + VSIZE[STORES[op][1]], 0
    if op == 0x0C or op == 0x0E or op == 0x0F or op == 0x00:
        return 0, 0
    if op == 0x0D:
        return 4, 0
    if op == 0x10:
        ps, rs = func_type(m, imm)
        return sum(VSIZE[t] for t in ps), sum(VSIZE[t] for t in rs)
    if op == 0x11:
        ps, rs = m.types[imm[0]]
        return sum(VSIZE[t] for t in ps), sum(VSIZE[t] for t in rs)   # quirk: index not popped
    if op == 0x1A:
        return imm, 0
    if op in (0x1B, 0x1C):
        return 2 * imm + 4, imm
    if op == 0x23:
        return 0, VSIZE[m.globals[imm][0]]
    if op == 0x24:
        return VSIZE[m.globals[imm][0]], 0
    if op == 0x3F:
        return 0, 4
    if op == 0x40:
        return 4, 4
    if op == 0x01:
        return 0, 0
    if op == 0x25:
        return 4, 8
    if op == 0x26:
        return 12, 0
    if op == 0xD0:
        return 0, 8
    if op == 0xD1:
        return 8, 4
    if op == 0xD2:
        return 0, 8
    if op in (0xFC08, 0xFC0A, 0xFC0B, 0xFC0C, 0xFC0E):
        return 12, 0
    if op in (0xFC09, 0xFC0D):
        return 0, 0
    if op == 0xFC0F:
        return 12, 4
    if op == 0xFC10:
        return 0, 4
    if op == 0xFC11:
        return 16, 0
    raise Unmodeled(f"stack effect {op:#x}")


def local_type(f, i):
    np_ = len(f.params)
    return f.params[i] if i < np_ else f.locals[i - np_]


# ----------------------------------------------------------------------------------------------
# Preparation

def prepare(b):
    """Returns module or raises PrepError / OutOfDomain / Unmodeled."""
    m = decode(b)
    if m.serialization_error:
        raise PrepError("Serialization")
    if m.has_float:
        # The module is valid but uses floats: everything after decoding (stack sizes, charge points,
        # execution) is outside the integer subset.
        raise OutOfDomain("float types or opcodes")
    defined = [f for f in m.funcs if not f.imported]
    total_params = 0
    total_blocks = 0
    for f in defined:
        analyse(m, f)
        if len(f.params) > MAX_PARAMS_FN:
            raise PrepError("TooManyParamsPerFunction")
        total_params += len(f.params)
        if total_params > MAX_PARAMS_CONTRACT:
            raise PrepError("TooManyParamsPerContract")
        if f.opmax > MAX_OPSTACK:
            raise PrepError("OperandStackTooLarge")
        if f.nblocks > MAX_BLOCKS_FN:
            raise PrepError("TooManyBlocksPerFunction")
        total_blocks += f.nblocks
        if total_blocks > MAX_BLOCKS_CONTRACT:
            raise PrepError("TooManyBlocksPerContract")
        f.frame = 64 + sum(VSIZE[t] for t in f.params) + sum(VSIZE[t] for t in f.locals)
    size = instrumented_size_estimate(m, b, defined)
    if size is not None and size > MAX_INSTRUMENTED:
        raise PrepError("InstrumentedCodeTooLarge")
    return m


def instrumented_size_estimate(m, b, defined):
    """InstrumentedCodeTooLarge.  The prose spec does not say how the instrumented module's size is computed,
    so this is a linear estimate fitted to the LENGTHS of nearcore's prepared modules (harness `prepare` mode,
    black box) over ~1,500 random contracts and the large opcode-corpus contracts; max relative error 0.7%.
    Within INSTR_SLACK of the limit we answer `unmodeled` instead of guessing."""
    est = len(b) + 154.2
    for f in defined:
        est += 63.0 + 2.66 * (sleb_len(((f.frame + 7) // 8) * R) + sleb_len(f.opmax + f.frame))
        for p in f.points:
            est += 59.1 if p[2] else 18.17 + 2.957 * sleb_len(p[1])
        est += 21.0 * sum(1 for pc, o in enumerate(f.ops) if o[0] == 0x0F and f.live[pc])
    if est * (1 - INSTR_SLACK) > MAX_INSTRUMENTED:
        return est
    if est * (1 + INSTR_SLACK) <= MAX_INSTRUMENTED:
        return est
    raise Unmodeled("instrumented size within estimate error of the 16 MiB limit")


INSTR_SLACK = 0.015


def sleb_len(v):
    n = 1
    while not (-64 <= v < 64):
        v >>= 7
        n += 1
    return n


# ----------------------------------------------------------------------------------------------
# Host function inventory (boundary doc, Appendix A): name -> (params, results); i = i64, I = i32

def _sig(s):
    p, r = s.split("->")
    tm = {"i": I64, "I": I32}
    return tuple(tm[c] for c in p), tuple(tm[c] for c in r)


HOST = {k: _sig(v) for k, v in {
    "read_register": "ii->", "register_len": "i->i", "write_register": "iii->",
    "current_account_id": "i->", "chain_id": "i->", "signer_account_id": "i->", "signer_account_pk": "i->",
    "predecessor_account_id": "i->", "refund_to_account_id": "i->", "input": "i->", "block_index": "->i",
    "block_timestamp": "->i", "epoch_height": "->i", "storage_usage": "->i", "current_contract_code": "i->i",
    "account_balance": "i->", "account_locked_balance": "i->", "attached_deposit": "i->", "prepaid_gas": "->i",
    "used_gas": "->i",
    "random_seed": "i->", "sha256": "iii->", "keccak256": "iii->", "keccak512": "iii->", "ripemd160": "iii->",
    "ecrecover": "iiiiiii->i", "ed25519_verify": "iiiiii->i", "p256_verify": "iiiiii->i",
    "alt_bn128_g1_multiexp": "iii->", "alt_bn128_g1_sum": "iii->", "alt_bn128_pairing_check": "ii->i",
    "bls12381_p1_sum": "iii->i", "bls12381_p2_sum": "iii->i", "bls12381_g1_multiexp": "iii->i",
    "bls12381_g2_multiexp": "iii->i", "bls12381_map_fp_to_g1": "iii->i", "bls12381_map_fp2_to_g2": "iii->i",
    "bls12381_pairing_check": "ii->i", "bls12381_p1_decompress": "iii->i", "bls12381_p2_decompress": "iii->i",
    "value_return": "ii->", "panic": "->", "panic_utf8": "ii->", "log_utf8": "ii->", "log_utf16": "ii->",
    "abort": "IIII->", "gas": "I->",
    "promise_create": "iiiiiiii->i", "promise_then": "iiiiiiiii->i", "promise_and": "ii->i",
    "promise_batch_create": "ii->i", "promise_batch_then": "iii->i", "promise_set_refund_to": "iii->",
    "promise_return": "i->",
    "promise_batch_action_create_account": "i->", "promise_batch_action_deploy_contract": "iii->",
    "promise_batch_action_deploy_global_contract": "iii->",
    "promise_batch_action_deploy_global_contract_by_account_id": "iii->",
    "promise_batch_action_use_global_contract": "iii->",
    "promise_batch_action_use_global_contract_by_account_id": "iii->",
    "promise_batch_action_state_init": "iiii->i", "promise_batch_action_state_init_by_account_id": "iiii->i",
    "set_state_init_data_entry": "iiiiii->",
    "promise_batch_action_function_call": "iiiiiii->", "promise_batch_action_function_call_weight": "iiiiiiii->",
    "promise_batch_action_transfer": "ii->", "promise_batch_action_stake": "iiii->",
    "promise_batch_action_add_key_with_full_access": "iiii->",
    "promise_batch_action_add_key_with_function_call": "iiiiiiiii->",
    "promise_batch_action_delete_key": "iii->", "promise_batch_action_delete_account": "iii->",
    "promise_batch_action_transfer_to_gas_key": "iiii->",
    "promise_batch_action_add_gas_key_with_full_access": "iiii->",
    "promise_batch_action_add_gas_key_with_function_call": "iiiiiiiii->",
    "promise_yield_create": "iiiiiii->i", "promise_yield_create_with_id": "iiiiiiiii->i",
    "promise_yield_resume": "iiii->I", "promise_yield_resume_with_yield_id": "iiii->I",
    "promise_results_count": "->i", "promise_result": "ii->i",
    "storage_write": "iiiii->i", "storage_read": "iii->i", "storage_remove": "iii->i", "storage_has_key": "ii->i",
    "storage_iter_prefix": "ii->i", "storage_iter_range": "iiii->i", "storage_iter_next": "iii->i",
    "validator_stake": "iii->", "validator_total_stake": "i->",
}.items()}
assert len(HOST) == 89


def wt_functype(ps, rs):
    s = "(func"
    if ps:
        s += " (param " + " ".join(TNAME[t] for t in ps) + ")"
    if rs:
        s += " (result " + " ".join(TNAME[t] for t in rs) + ")"
    return s + ")"


# ----------------------------------------------------------------------------------------------
# Gas counter (prose spec §4, boundary doc Appendix A §3)

class GasCounter:
    __slots__ = ("prepaid", "burnt", "promises", "limit")

    def __init__(self, prepaid):
        self.prepaid = prepaid
        self.burnt = 0
        self.promises = 0
        self.limit = min(MAX_GAS_BURNT, prepaid)

    def _fail(self, new_burnt, new_used):
        self.burnt = min(new_burnt, min(self.prepaid, MAX_GAS_BURNT))
        self.promises = max(0, min(self.prepaid, new_used) - self.burnt)
        raise HostErr("GasLimitExceeded" if new_burnt > MAX_GAS_BURNT else "GasExceeded")

    def burn(self, x):
        nb = self.burnt + x
        if nb > U64:
            raise HostErr("IntegerOverflow")
        if nb <= self.limit:
            self.burnt = nb
            return
        self._fail(nb, nb + self.promises)

    def pay_base(self, c):
        self.burn(c)

    def pay_per(self, c, n):
        x = c * n
        if x > U64:
            raise HostErr("IntegerOverflow")
        self.burn(x)

    def deduct(self, burn, use):
        nb = self.burnt + burn
        if nb > U64:
            raise HostErr("IntegerOverflow")
        nu = nb + self.promises + (use - burn)
        if nu > U64:
            raise HostErr("IntegerOverflow")
        if nb <= MAX_GAS_BURNT and nu <= self.prepaid:
            self.burnt = nb
            self.promises += use - burn
            if use > burn:
                self.limit = min(MAX_GAS_BURNT, self.prepaid - self.promises)
            return
        self._fail(nb, nu)

    def remaining(self):
        return self.prepaid - self.burnt - self.promises


# ----------------------------------------------------------------------------------------------
# Account id validation (NEAR rules)

def valid_account_id(s):
    if not (2 <= len(s) <= 64):
        return False
    prev_sep = True
    for ch in s:
        if ch in "-_.":
            if prev_sep:
                return False
            prev_sep = True
        elif "a" <= ch <= "z" or "0" <= ch <= "9":
            prev_sep = False
        else:
            return False
    return not prev_sep


# ----------------------------------------------------------------------------------------------
# Compilation to an internal instruction stream

(O_LGET, O_CONST, O_BIN, O_LSET, O_LTEE, O_UN, O_CHARGE, O_BRIF, O_BR, O_LOAD, O_STORE, O_GGET, O_GSET,
 O_DROP, O_SELECT, O_IF, O_JMP, O_CALL, O_RET, O_CHARGEL, O_BRTABLE, O_CALLIND, O_MSIZE, O_MGROW, O_UNREACH,
 O_MFILL, O_MCOPY, O_MINIT, O_DDROP, O_TGET, O_TSET, O_TSIZE, O_TGROW, O_TFILL, O_TCOPY, O_TINIT, O_EDROP,
 O_REFNULL, O_ISNULL, O_REFFUNC) = range(40)

M32 = 0xFFFFFFFF
M64 = U64


def s32(v):
    return v - (1 << 32) if v & 0x80000000 else v


def s64(v):
    return v - (1 << 64) if v & (1 << 63) else v


def _divs(a, b, bits):
    if b == 0:
        raise Trap("IllegalArithmetic")
    q = abs(a) // abs(b)
    if (a < 0) != (b < 0):
        q = -q
    if q >= 1 << (bits - 1):
        raise Trap("IllegalArithmetic")
    return q


def _rems(a, b):
    if b == 0:
        raise Trap("IllegalArithmetic")
    rr = abs(a) % abs(b)
    return -rr if a < 0 else rr


def _rot(a, k, bits, left):
    k %= bits
    m = (1 << bits) - 1
    if not left:
        k = (bits - k) % bits
    return ((a << k) | (a >> (bits - k))) & m


def _clz(a, bits):
    return bits - a.bit_length()


def _ctz(a, bits):
    if a == 0:
        return bits
    return (a & -a).bit_length() - 1


def _sext(a, frm, to):
    a &= (1 << frm) - 1
    if a & (1 << (frm - 1)):
        a -= 1 << frm
    return a & ((1 << to) - 1)


def _divu(a, b):
    if b == 0:
        raise Trap("IllegalArithmetic")
    return a // b


def _remu(a, b):
    if b == 0:
        raise Trap("IllegalArithmetic")
    return a % b


BINF = {
    0x46: lambda a, b: 1 if a == b else 0, 0x47: lambda a, b: 1 if a != b else 0,
    0x48: lambda a, b: 1 if s32(a) < s32(b) else 0, 0x49: lambda a, b: 1 if a < b else 0,
    0x4A: lambda a, b: 1 if s32(a) > s32(b) else 0, 0x4B: lambda a, b: 1 if a > b else 0,
    0x4C: lambda a, b: 1 if s32(a) <= s32(b) else 0, 0x4D: lambda a, b: 1 if a <= b else 0,
    0x4E: lambda a, b: 1 if s32(a) >= s32(b) else 0, 0x4F: lambda a, b: 1 if a >= b else 0,
    0x51: lambda a, b: 1 if a == b else 0, 0x52: lambda a, b: 1 if a != b else 0,
    0x53: lambda a, b: 1 if s64(a) < s64(b) else 0, 0x54: lambda a, b: 1 if a < b else 0,
    0x55: lambda a, b: 1 if s64(a) > s64(b) else 0, 0x56: lambda a, b: 1 if a > b else 0,
    0x57: lambda a, b: 1 if s64(a) <= s64(b) else 0, 0x58: lambda a, b: 1 if a <= b else 0,
    0x59: lambda a, b: 1 if s64(a) >= s64(b) else 0, 0x5A: lambda a, b: 1 if a >= b else 0,
    0x6A: lambda a, b: (a + b) & M32, 0x6B: lambda a, b: (a - b) & M32, 0x6C: lambda a, b: (a * b) & M32,
    0x6D: lambda a, b: _divs(s32(a), s32(b), 32) & M32, 0x6E: _divu,
    0x6F: lambda a, b: _rems(s32(a), s32(b)) & M32, 0x70: _remu,
    0x71: lambda a, b: a & b, 0x72: lambda a, b: a | b, 0x73: lambda a, b: a ^ b,
    0x74: lambda a, b: (a << (b & 31)) & M32, 0x75: lambda a, b: (s32(a) >> (b & 31)) & M32,
    0x76: lambda a, b: a >> (b & 31), 0x77: lambda a, b: _rot(a, b, 32, True),
    0x78: lambda a, b: _rot(a, b, 32, False),
    0x7C: lambda a, b: (a + b) & M64, 0x7D: lambda a, b: (a - b) & M64, 0x7E: lambda a, b: (a * b) & M64,
    0x7F: lambda a, b: _divs(s64(a), s64(b), 64) & M64, 0x80: _divu,
    0x81: lambda a, b: _rems(s64(a), s64(b)) & M64, 0x82: _remu,
    0x83: lambda a, b: a & b, 0x84: lambda a, b: a | b, 0x85: lambda a, b: a ^ b,
    0x86: lambda a, b: (a << (b & 63)) & M64, 0x87: lambda a, b: (s64(a) >> (b & 63)) & M64,
    0x88: lambda a, b: a >> (b & 63), 0x89: lambda a, b: _rot(a, b, 64, True),
    0x8A: lambda a, b: _rot(a, b, 64, False),
}
UNF = {
    0x45: lambda a: 1 if a == 0 else 0, 0x50: lambda a: 1 if a == 0 else 0,
    0x67: lambda a: _clz(a, 32), 0x68: lambda a: _ctz(a, 32), 0x69: lambda a: bin(a).count("1"),
    0x79: lambda a: _clz(a, 64), 0x7A: lambda a: _ctz(a, 64), 0x7B: lambda a: bin(a).count("1"),
    0xA7: lambda a: a & M32, 0xAC: lambda a: _sext(a, 32, 64), 0xAD: lambda a: a,
    0xC0: lambda a: _sext(a, 8, 32), 0xC1: lambda a: _sext(a, 16, 32),
    0xC2: lambda a: _sext(a, 8, 64), 0xC3: lambda a: _sext(a, 16, 64), 0xC4: lambda a: _sext(a, 32, 64),
}
LOADSTRUCT = {0x28: ("<I", 0), 0x29: ("<Q", 0), 0x2C: ("<b", M32), 0x2D: ("<B", 0), 0x2E: ("<h", M32),
              0x2F: ("<H", 0), 0x30: ("<b", M64), 0x31: ("<B", 0), 0x32: ("<h", M64), 0x33: ("<H", 0),
              0x34: ("<i", M64), 0x35: ("<I", 0)}
STORESTRUCT = {0x36: ("<I", M32), 0x37: ("<Q", M64), 0x3A: ("<B", 0xFF), 0x3B: ("<H", 0xFFFF),
               0x3C: ("<B", 0xFF), 0x3D: ("<H", 0xFFFF), 0x3E: ("<I", M32)}


def compile_func(m, f):
    ops = f.ops
    live = f.live
    n = len(ops)
    pts = {p[0]: p for p in f.points}
    code = []
    idx_of = [0] * (n + 1)
    fixups = []   # (code index, slot, kind, ctrl) kind: 'after_end' | 'after_else' | 'loop_body'
    code.append((O_CHARGE, ((f.frame + 7) // 8) * R))
    for pc, (op, imm, info, h_after) in enumerate(ops[:n]):
        idx_of[pc] = len(code)
        if not live[pc]:
            continue
        p = pts.get(pc)
        if p is not None:
            if p[2]:
                code.append((O_CHARGEL, p[1], p[2]))
            else:
                code.append((O_CHARGE, p[1]))
        if op == 0x20:
            code.append((O_LGET, imm))
        elif op == 0x41 or op == 0x42:
            code.append((O_CONST, imm))
        elif op in BINF:
            code.append((O_BIN, BINF[op]))
        elif op in UNF:
            code.append((O_UN, UNF[op]))
        elif op == 0x21:
            code.append((O_LSET, imm))
        elif op == 0x22:
            code.append((O_LTEE, imm))
        elif op in LOADSTRUCT:
            st, sm = LOADSTRUCT[op]
            code.append((O_LOAD, struct.Struct(st), imm, LOADS[op][2], sm))
        elif op in STORESTRUCT:
            st, sm = STORESTRUCT[op]
            code.append((O_STORE, struct.Struct(st), imm, STORES[op][2], sm))
        elif op == 0x23:
            code.append((O_GGET, imm))
        elif op == 0x24:
            code.append((O_GSET, imm))
        elif op == 0x1A:
            code.append((O_DROP,))
        elif op in (0x1B, 0x1C):
            code.append((O_SELECT,))
        elif op in (0x02, 0x03, 0x01):
            pass
        elif op == 0x04:
            fixups.append((len(code), info, "if"))
            code.append(None)
        elif op == 0x05:
            fixups.append((len(code), info, "else"))
            code.append(None)
        elif op == 0x0B:
            if info.kind == "func":
                code.append((O_RET, len(f.results)))
        elif op == 0x0C or op == 0x0D:
            c, keep = info
            fixups.append((len(code), (c, keep, h_after if op == 0x0C else None), "br" if op == 0x0C else "brif"))
            code.append(None)
        elif op == 0x0E:
            fixups.append((len(code), info, "brtable"))
            code.append(None)
        elif op == 0x0F:
            code.append((O_RET, len(f.results)))
        elif op == 0x10:
            code.append((O_CALL, imm))
        elif op == 0x11:
            ps, rs = m.types[imm[0]]
            code.append((O_CALLIND, (ps, rs), imm[1]))
        elif op == 0x3F:
            code.append((O_MSIZE,))
        elif op == 0x40:
            code.append((O_MGROW,))
        elif op == 0x00:
            code.append((O_UNREACH,))
        elif op == 0xFC0B:
            code.append((O_MFILL,))
        elif op == 0xFC0A:
            code.append((O_MCOPY,))
        elif op == 0xFC08:
            code.append((O_MINIT, imm))
        elif op == 0xFC09:
            code.append((O_DDROP, imm))
        elif op == 0x25:
            code.append((O_TGET, imm))
        elif op == 0x26:
            code.append((O_TSET, imm))
        elif op == 0xFC10:
            code.append((O_TSIZE, imm))
        elif op == 0xFC0F:
            code.append((O_TGROW, imm))
        elif op == 0xFC11:
            code.append((O_TFILL, imm))
        elif op == 0xFC0E:
            code.append((O_TCOPY, imm))
        elif op == 0xFC0C:
            code.append((O_TINIT, imm))
        elif op == 0xFC0D:
            code.append((O_EDROP, imm))
        elif op == 0xD0:
            code.append((O_REFNULL,))
        elif op == 0xD1:
            code.append((O_ISNULL,))
        elif op == 0xD2:
            code.append((O_REFFUNC, imm))
        else:
            raise Unmodeled(f"opcode {op:#x}")
    idx_of[n] = len(code)

    def after_end(c):
        return idx_of[c.end_pc + 1] if c.kind != "func" else None

    def br_target(c, keep):
        if c.kind == "loop":
            return (idx_of[c.pc + 1], c.height, keep)
        if c.kind == "func":
            return (None, 0, keep)
        return (after_end(c), c.height, keep)

    for ci, info, kind in fixups:
        if kind == "if":
            c = info
            tgt = idx_of[c.else_pc + 1] if c.else_pc is not None else after_end(c)
            code[ci] = (O_IF, tgt)
        elif kind == "else":
            code[ci] = (O_JMP, after_end(info))
        elif kind in ("br", "brif"):
            c, keep, _ = info
            t, h, k = br_target(c, keep)
            if t is None:
                code[ci] = (O_RET, len(f.results)) if kind == "br" else (O_BRIF, None, 0, k)
            else:
                code[ci] = (O_BR if kind == "br" else O_BRIF, t, h, k)
        elif kind == "brtable":
            tl, cd, arity = info
            code[ci] = (O_BRTABLE, [br_target(c, arity) for c in tl], br_target(cd, arity))
    f.code = code


# ----------------------------------------------------------------------------------------------
# Instance and execution

class Instance:
    pass


def fail_gas(inst, a):
    """A charge point whose amount exceeds the wasm-side gas copy."""
    gc = inst.gc
    gc.burnt = gc.prepaid - gc.promises - inst.g          # sync (always succeeds)
    try:
        gc.burn(a)
    except HostErr as e:
        e.synced = True
        inst.g = gc.remaining()
        raise
    raise Unmodeled("charge point unexpectedly succeeded")


def execute(inst, entry):
    """Run function `entry` from the host (no args, no results).  Raises Trap/HostErr/Unmodeled."""
    m = inst.m
    funcs = m.funcs
    mem = inst.mem
    globs = inst.globals
    gc = inst.gc
    g = gc.remaining()
    inst.g = g
    stk = []
    frames = []
    memlen = inst.memlen
    f = funcs[entry]
    try:
        # function entry (prologue stack part)
        cost = f.opmax + f.frame
        inst.stack -= cost
        if inst.stack < 0:
            raise HostErr("MemoryAccessViolation")
        code = f.code
        L = [0] * len(f.locals)
        for i, t in enumerate(f.locals):
            if t == FUNCREF:
                L[i] = None
        base = 0
        pc = 0
        cur = f
        while True:
            ins = code[pc]
            pc += 1
            op = ins[0]
            if op == O_LGET:
                stk.append(L[ins[1]])
            elif op == O_CONST:
                stk.append(ins[1])
            elif op == O_BIN:
                b = stk.pop()
                stk[-1] = ins[1](stk[-1], b)
            elif op == O_LSET:
                L[ins[1]] = stk.pop()
            elif op == O_LTEE:
                L[ins[1]] = stk[-1]
            elif op == O_UN:
                stk[-1] = ins[1](stk[-1])
            elif op == O_CHARGE:
                a = ins[1]
                if a <= g:
                    g -= a
                else:
                    inst.g = g
                    fail_gas(inst, a)
            elif op == O_BRIF:
                if stk.pop():
                    t = ins[1]
                    if t is None:
                        op = O_RET
                        ins = (O_RET, ins[3])
                    else:
                        keep = ins[3]
                        h = base + ins[2]
                        if keep:
                            if len(stk) - keep != h:
                                v = stk[-keep:]
                                del stk[h:]
                                stk.extend(v)
                        else:
                            del stk[h:]
                        pc = t
                        continue
                else:
                    continue
            elif op == O_BR:
                keep = ins[3]
                h = base + ins[2]
                if keep:
                    if len(stk) - keep != h:
                        v = stk[-keep:]
                        del stk[h:]
                        stk.extend(v)
                else:
                    del stk[h:]
                pc = ins[1]
                continue
            elif op == O_LOAD:
                ea = stk[-1] + ins[2]
                if ea + ins[3] > memlen:
                    raise Trap("MemoryOutOfBounds")
                v = ins[1].unpack_from(mem, ea)[0]
                if ins[4] and v < 0:
                    v &= ins[4]
                stk[-1] = v
                continue
            elif op == O_STORE:
                v = stk.pop()
                ea = stk.pop() + ins[2]
                if ea + ins[3] > memlen:
                    raise Trap("MemoryOutOfBounds")
                ins[1].pack_into(mem, ea, v & ins[4])
                continue
            elif op == O_GGET:
                stk.append(globs[ins[1]])
                continue
            elif op == O_GSET:
                globs[ins[1]] = stk.pop()
                continue
            elif op == O_DROP:
                stk.pop()
                continue
            elif op == O_SELECT:
                c = stk.pop()
                b = stk.pop()
                if not c:
                    stk[-1] = b
                continue
            elif op == O_IF:
                if not stk.pop():
                    pc = ins[1]
                continue
            elif op == O_JMP:
                pc = ins[1]
                continue
            elif op == O_CALL or op == O_CALLIND:
                if op == O_CALL:
                    callee = funcs[ins[1]]
                else:
                    i = stk.pop()
                    tab = inst.tables[ins[2]]
                    if i >= len(tab):
                        raise Trap("MemoryOutOfBounds")
                    fi = tab[i]
                    if fi is None:
                        raise Trap("IndirectCallToNull")
                    callee = funcs[fi]
                    if (callee.params, callee.results) != ins[1]:
                        raise Trap("IncorrectCallIndirectSignature")
                if callee.imported:
                    np_ = len(callee.params)
                    args = stk[len(stk) - np_:] if np_ else []
                    if np_:
                        del stk[len(stk) - np_:]
                    inst.g = g
                    res = host_call(inst, callee, args)
                    g = inst.g
                    if res is not None:
                        stk.append(res)
                    continue
                cost = callee.opmax + callee.frame
                inst.stack -= cost
                if inst.stack < 0:
                    raise HostErr("MemoryAccessViolation")
                np_ = len(callee.params)
                frames.append((code, pc, L, base, cur))
                if np_:
                    NL = stk[len(stk) - np_:]
                    del stk[len(stk) - np_:]
                else:
                    NL = []
                for t in callee.locals:
                    NL.append(None if t == FUNCREF else 0)
                L = NL
                base = len(stk)
                code = callee.code
                cur = callee
                pc = 0
                continue
            elif op == O_CHARGEL:
                a = ins[1] + ins[2] * stk[-1]
                if a <= g:
                    g -= a
                else:
                    inst.g = g
                    fail_gas(inst, a)
                continue
            elif op == O_BRTABLE:
                i = stk.pop()
                tl = ins[1]
                t, h, keep = tl[i] if i < len(tl) else ins[2]
                if t is None:
                    op = O_RET
                    ins = (O_RET, keep)
                else:
                    h += base
                    if keep:
                        v = stk[-keep:]
                        del stk[h:]
                        stk.extend(v)
                    else:
                        del stk[h:]
                    pc = t
                    continue
            elif op == O_MSIZE:
                stk.append(memlen // PAGE)
                continue
            elif op == O_MGROW:
                d = stk[-1]
                old = memlen // PAGE
                if old + d > MEM_MAX_PAGES:
                    stk[-1] = M32
                else:
                    memlen += d * PAGE
                    inst.memlen = memlen
                    stk[-1] = old
                continue
            elif op == O_UNREACH:
                raise Trap("Unreachable")
            elif op == O_MFILL:
                n = stk.pop()
                v = stk.pop()
                d = stk.pop()
                if d + n > memlen:
                    raise Trap("MemoryOutOfBounds")
                mem[d:d + n] = bytes([v & 0xFF]) * n
                continue
            elif op == O_MCOPY:
                n = stk.pop()
                s = stk.pop()
                d = stk.pop()
                if s + n > memlen or d + n > memlen:
                    raise Trap("MemoryOutOfBounds")
                mem[d:d + n] = mem[s:s + n]
                continue
            elif op == O_MINIT:
                n = stk.pop()
                s = stk.pop()
                d = stk.pop()
                seg = inst.datas[ins[1]]
                if s + n > len(seg) or d + n > memlen:
                    raise Trap("MemoryOutOfBounds")
                mem[d:d + n] = seg[s:s + n]
                continue
            elif op == O_DDROP:
                inst.datas[ins[1]] = b""
                continue
            elif op == O_TGET:
                i = stk[-1]
                tab = inst.tables[ins[1]]
                if i >= len(tab):
                    raise Trap("MemoryOutOfBounds")
                stk[-1] = tab[i]
                continue
            elif op == O_TSET:
                v = stk.pop()
                i = stk.pop()
                tab = inst.tables[ins[1]]
                if i >= len(tab):
                    raise Trap("MemoryOutOfBounds")
                tab[i] = v
                continue
            elif op == O_TSIZE:
                stk.append(len(inst.tables[ins[1]]))
                continue
            elif op == O_TGROW:
                n = stk.pop()
                v = stk[-1]
                tab = inst.tables[ins[1]]
                old = len(tab)
                if old + n > inst.table_max[ins[1]]:
                    stk[-1] = M32
                else:
                    tab.extend([v] * n)
                    stk[-1] = old
                continue
            elif op == O_TFILL:
                n = stk.pop()
                v = stk.pop()
                i = stk.pop()
                tab = inst.tables[ins[1]]
                if i + n > len(tab):
                    raise Trap("MemoryOutOfBounds")
                for k in range(i, i + n):
                    tab[k] = v
                continue
            elif op == O_TCOPY:
                n = stk.pop()
                s = stk.pop()
                d = stk.pop()
                td = inst.tables[ins[1][0]]
                ts = inst.tables[ins[1][1]]
                if s + n > len(ts) or d + n > len(td):
                    raise Trap("MemoryOutOfBounds")
                td[d:d + n] = ts[s:s + n]
                continue
            elif op == O_TINIT:
                n = stk.pop()
                s = stk.pop()
                d = stk.pop()
                seg = inst.elems[ins[1][0]]
                tab = inst.tables[ins[1][1]]
                if s + n > len(seg) or d + n > len(tab):
                    raise Trap("MemoryOutOfBounds")
                tab[d:d + n] = seg[s:s + n]
                continue
            elif op == O_EDROP:
                inst.elems[ins[1]] = []
                continue
            elif op == O_REFNULL:
                stk.append(None)
                continue
            elif op == O_ISNULL:
                stk[-1] = 1 if stk[-1] is None else 0
                continue
            elif op == O_REFFUNC:
                stk.append(ins[1])
                continue
            if op == O_RET:
                keep = ins[1]
                inst.stack += cur.opmax + cur.frame
                if keep:
                    v = stk[-1]
                    del stk[base:]
                    stk.append(v)
                else:
                    del stk[base:]
                if not frames:
                    break
                code, pc, L, base, cur = frames.pop()
    except Exception as e:
        if not getattr(e, "synced", False):
            inst.g = g
        raise
    inst.g = g


def sync_exit(inst):
    """Return from wasm to the host: burn what the wasm-side counter consumed."""
    gc = inst.gc
    x = gc.remaining() - inst.g
    if x < 0:
        raise Unmodeled("negative sync")
    gc.burn(x)


# ----------------------------------------------------------------------------------------------
# Host functions

def mem_read(inst, ptr, n):
    gc = inst.gc
    gc.pay_base(C_READ_MEM_BASE)
    gc.pay_per(C_READ_MEM_BYTE, n)
    end = ptr + n
    if end > inst.memlen:
        raise HostErr("MemoryAccessViolation")
    return bytes(inst.mem[ptr:end])


def mem_or_register(inst, ptr, n):
    if n == U64:
        # read a register; no registers are ever written in the modelled host subset
        raise HostErr(f"InvalidRegisterId {{ register_id: {ptr} }}")
    return mem_read(inst, ptr, n)


def read_account_id(inst, n, ptr):
    gc = inst.gc
    data = mem_or_register(inst, ptr, n)
    gc.pay_base(C_UTF8_BASE)
    gc.pay_per(C_UTF8_BYTE, n)
    try:
        s = data.decode("utf-8")
    except UnicodeDecodeError:
        raise HostErr("BadUTF8")
    if not valid_account_id(s):
        raise HostErr("InvalidAccountId")
    return data


def fee_send(fee, sir):
    return fee[0] if sir else fee[1]


def host_call(inst, f, args):
    gc = inst.gc
    # sync before the call
    gc.burnt = gc.prepaid - gc.promises - inst.g
    try:
        res = host_dispatch(inst, f.imp_name, args)
    except Exception as e:
        e.synced = True
        inst.g = gc.remaining()
        raise
    inst.g = gc.remaining()
    return res


def host_dispatch(inst, name, a):
    gc = inst.gc
    if name == "value_return":
        n, ptr = a
        gc.pay_base(C_BASE)
        data = mem_or_register(inst, ptr, n)
        if len(data) > MAX_RETURNED_DATA:
            raise HostErr(f"ReturnedValueLengthExceeded {{ length: {len(data)}, limit: {MAX_RETURNED_DATA} }}")
        burn = 0
        for rcv in inst.receivers:
            sir = rcv == CURRENT_ACCOUNT
            burn += (fee_send(F_DATA_RECEIPT_BYTE, sir) + F_DATA_RECEIPT_BYTE[2]) * len(data)
        if burn > U64:
            raise HostErr("IntegerOverflow")
        gc.deduct(burn, burn)
        inst.ret = data
        return None
    if name == "panic":
        gc.pay_base(C_BASE)
        raise HostErr('GuestPanic { panic_msg: "explicit guest panic" }')
    if name == "gas":
        gc.pay_per(R, a[0])
        return None
    if name == "promise_batch_create":
        n, ptr = a
        gc.pay_base(C_BASE)
        acc = read_account_id(inst, n, ptr)
        sir = acc == CURRENT_ACCOUNT
        gc.deduct(fee_send(F_NEW_ACTION_RECEIPT, sir), fee_send(F_NEW_ACTION_RECEIPT, sir) + F_NEW_ACTION_RECEIPT[2])
        if len(inst.promises) >= MAX_PROMISES:
            raise HostErr(f"NumberPromisesExceeded {{ number_of_promises: {len(inst.promises) + 1}, "
                          f"limit: {MAX_PROMISES} }}")
        inst.promises.append(acc)
        return len(inst.promises) - 1
    if name == "promise_batch_action_function_call":
        idx, mlen, mptr, alen, aptr, amt_ptr, gas = a
        gc.pay_base(C_BASE)
        amount = int.from_bytes(mem_read(inst, amt_ptr, 16), "little")
        method = mem_or_register(inst, mptr, mlen)
        if not method:
            raise HostErr("EmptyMethodName")
        args = mem_or_register(inst, aptr, alen)
        if idx >= len(inst.promises):
            raise HostErr(f"InvalidPromiseIndex {{ promise_idx: {idx} }}")
        acc = inst.promises[idx]
        sir = acc == CURRENT_ACCOUNT
        gc.deduct(fee_send(F_FUNCTION_CALL, sir), fee_send(F_FUNCTION_CALL, sir) + F_FUNCTION_CALL[2])
        nb = len(method) + len(args)
        b = fee_send(F_FUNCTION_CALL_BYTE, sir) * nb
        e = F_FUNCTION_CALL_BYTE[2] * nb
        gc.deduct(b, b + e)
        gc.deduct(0, gas)
        if amount == 1 and inst.balance == 0:
            pass        # one-yocto exemption (PV85 `one_yocto_on_promise`): subsidised, balance unchanged
        elif amount > inst.balance:
            raise HostErr("BalanceExceeded")
        else:
            inst.balance -= amount
        return None
    raise Unmodeled(f"host function {name}")


# ----------------------------------------------------------------------------------------------
# Running a contract

def run_case(prepaid, wasm, receivers):
    try:
        m = prepare(wasm)
    except PrepError as e:
        return f"abort 0 0 CompilationError(PrepareError({e.args[0]}))"
    except OutOfDomain as e:
        return f"out-of-domain {e.args[0]}"
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    defined = [f for f in m.funcs if not f.imported]
    for f in defined:
        if len(f.params) + len(f.locals) > ENGINE_LOCALS:
            return (f"abort 0 0 CompilationError(WasmtimeCompileError {{ msg: \"failed to compile: "
                    f"wasm[0]::function[{f.idx + 3}]\" }})")
    if prepaid > MAX_GAS_BURNT:
        return "unmodeled prepaid above max_gas_burnt"
    gc = GasCounter(prepaid)

    def abort(err):
        return f"abort {gc.burnt} {gc.burnt + gc.promises} {err}"

    # loading fee
    try:
        gc.pay_per(LOAD_BYTES, len(wasm))
        gc.pay_base(LOAD_BASE)
    except HostErr:
        return abort("HostError(GasExceeded)")
    # link
    for nm, t in m.imports:
        if nm not in HOST:
            return abort('LinkError { msg: "unknown or invalid import" }')
        if HOST[nm] != m.types[t]:
            want = wt_functype(*m.types[t])
            have = wt_functype(*HOST[nm])
            return abort(f'LinkError {{ msg: "types incompatible: expected type `{want}`, found type `{have}`" }}')
    # method resolution
    ex = m.exports.get("main")
    if ex is None or ex[0] != 0:
        return "abort 0 0 MethodResolveError(MethodNotFound)"
    mainf = m.funcs[ex[1]]
    if (mainf.params, mainf.results) != ((), ()):
        return "abort 0 0 MethodResolveError(MethodInvalidSignature)"
    try:
        for f in defined:
            compile_func(m, f)
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    inst = Instance()
    inst.m = m
    inst.gc = gc
    inst.g = gc.remaining()
    inst.stack = STACK_BUDGET
    inst.receivers = [r.encode() for r in receivers]
    inst.ret = None
    inst.promises = []
    inst.balance = BALANCE
    inst.mem = mmap.mmap(-1, MEM_MAX_PAGES * PAGE)
    inst.memlen = MEM_INIT_PAGES * PAGE
    inst.globals = [g[2] for g in m.globals]
    inst.tables = [[None] * mn for mn, mx in m.tables]
    inst.table_max = [min(TABLE_CAP, mx if mx is not None else TABLE_CAP) for mn, mx in m.tables]
    inst.elems = [list(items) if mode == "passive" or mode == "active" else [] for mode, t, off, items in m.elems]
    inst.datas = [d for mode, off, d in m.datas]
    try:
        # instantiation: element segments then data segments
        for k, (mode, t, off, items) in enumerate(m.elems):
            if mode == "active":
                tab = inst.tables[t]
                if off + len(items) > len(tab):
                    raise Trap("MemoryOutOfBounds")
                tab[off:off + len(items)] = items
                inst.elems[k] = []
            elif mode == "declarative":
                inst.elems[k] = []
        for k, (mode, off, d) in enumerate(m.datas):
            if mode == "active":
                if off + len(d) > inst.memlen:
                    raise Trap("MemoryOutOfBounds")
                inst.mem[off:off + len(d)] = d
                inst.datas[k] = b""
    except Trap as e:
        return abort(f"WasmTrap({e.args[0]})")
    try:
        for entry in ([m.start] if m.start is not None else []) + [ex[1]]:
            try:
                if m.funcs[entry].imported:
                    inst.g = gc.remaining()
                    host_call(inst, m.funcs[entry], [])
                else:
                    execute(inst, entry)
            finally:
                sync_exit(inst)
    except Trap as e:
        return abort(f"WasmTrap({e.args[0]})")
    except HostErr as e:
        return abort(f"HostError({e.args[0]})")
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    except RecursionError:
        return "unmodeled python recursion"
    ret = "-" if inst.ret is None else inst.ret.hex()
    return f"ok {gc.burnt} {gc.burnt + gc.promises} {ret} {inst.balance}"


def charge_points_line(wasm):
    try:
        m = prepare(wasm)
    except PrepError as e:
        return f"prepare-error {e.args[0]}"
    except OutOfDomain:
        return "out-of-domain"
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    parts = []
    for i, f in enumerate([f for f in m.funcs if not f.imported]):
        parts.append(f"f{i}:" + "".join(f" {p[0]}:{p[1]}:{p[2]}" for p in f.points))
    return " | ".join(parts)


def main():
    sys.setrecursionlimit(100000)
    cp = "--charge-points" in sys.argv[1:]
    out = sys.stdout
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        parts = line.split(" ")
        prepaid = int(parts[0])
        wasm = bytes.fromhex(parts[1])
        receivers = parts[2].split(",") if len(parts) > 2 and parts[2] else []
        try:
            if cp:
                res = charge_points_line(wasm)
            else:
                res = run_case(prepaid, wasm, receivers)
        except Exception as e:  # never crash the stream
            res = f"unmodeled internal error {type(e).__name__}: {e}"
        out.write(res + "\n")
        out.flush()


if __name__ == "__main__":
    main()
