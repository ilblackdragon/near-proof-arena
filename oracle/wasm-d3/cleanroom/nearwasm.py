#!/usr/bin/env python3
"""Clean-room NEAR PV86 WASM contract execution (D3-alpha integer subset).

Written from docs/research/near-wasm-prose-spec.md, docs/research/near-wasm-boundary.md (Appendix A)
and the WebAssembly 2.0 specification only; ambiguities were resolved by black-box runs of the nearcore
harness (see README.md).  Standard library only.

  nearwasm.py [--charge-points | --full] [--trace] < cases
  nearwasm.py --chunk CODEHEX_FILE [--deltas] < trace   # trie-backed chunk replay (nearstore.py, README 3b/3c)

Input lines: `<prepaid_gas> <wasm_hex> [<receivers> | k=v;...]` (the harness's context options: rcv, input,
results, deposit, balance).
Output: one outcome line per input line (`ok <burnt> <used> <ret|-|receipt<i>> <balance>` /
`abort <burnt> <used> <err>`); with --full, the harness `full` suffix
` || compute <n> || logs <hex,...> || actions <a;...> || trie <k=v,...>`; with --charge-points, one line of
per-function charge points.  --trace prints every host call to stderr.  Curve host functions (alt_bn128_*,
bls12381_*, ecrecover, p256_verify) give `out-of-domain`.
"""
import hashlib
import mmap
import re
import struct
import sys
import unicodedata

import nearcrypto
import nearstore

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

if nearstore.HOST_ERR is Exception:   # first import wins (nearstore re-imports nearwasm when run as __main__)
    nearstore.HOST_ERR = HostErr


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
        # quirk (README D15): as many values are popped as the callee has params, counted from the top,
        # where the table index sits; so the index and params[1:] are popped and params[0] stays counted
        # (the index stays when there are no params).
        return (4 + sum(VSIZE[t] for t in ps[1:]) if ps else 0), sum(VSIZE[t] for t in rs)
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
    if x:
        gc.burn(x)


# ----------------------------------------------------------------------------------------------
# Host functions (boundary doc Appendix A; orders of charges and checks settled by black-box runs,
# see README "Host functions: ambiguities")


# ExtCosts: name -> (gas, compute).  Compute differs from gas only for the storage/trie costs.
EXT = {
    "base": 264_768_111,
    "contract_loading_base": 35_445_963, "contract_loading_bytes": 1_089_295,
    "read_memory_base": 2_609_863_200, "read_memory_byte": 3_801_333,
    "write_memory_base": 2_803_794_861, "write_memory_byte": 2_723_772,
    "read_register_base": 2_517_165_186, "read_register_byte": 98_562,
    "write_register_base": 2_865_522_486, "write_register_byte": 3_801_564,
    "utf8_decoding_base": 3_111_779_061, "utf8_decoding_byte": 291_580_479,
    "utf16_decoding_base": 3_543_313_050, "utf16_decoding_byte": 163_577_493,
    "sha256_base": 4_540_970_250, "sha256_byte": 24_117_351,
    "keccak256_base": 5_879_491_275, "keccak256_byte": 21_471_105,
    "keccak512_base": 5_811_388_236, "keccak512_byte": 36_649_701,
    "ripemd160_base": 853_675_086, "ripemd160_block": 680_107_584,
    "ed25519_verify_base": 210_000_000_000, "ed25519_verify_byte": 9_000_000,
    "log_base": 3_543_313_050, "log_byte": 13_198_791,
    "storage_write_base": (64_196_736_000, 200_000_000_000), "storage_write_key_byte": 70_482_867,
    "storage_write_value_byte": 31_018_539, "storage_write_evicted_byte": 32_117_307,
    "storage_read_base": (56_356_845_749, 159_000_000_000), "storage_read_key_byte": (30_952_533, 10_000_000),
    "storage_read_value_byte": (5_611_004, 2_500_000),
    "storage_large_read_overhead_base": (1, 41_000_000_000), "storage_large_read_overhead_byte": (1, 3_111_005),
    "storage_remove_base": (53_473_030_500, 200_000_000_000), "storage_remove_key_byte": 38_220_384,
    "storage_remove_ret_value_byte": 11_531_556,
    "storage_has_key_base": (54_039_896_625, 158_000_000_000), "storage_has_key_byte": (30_790_845, 10_000_000),
    "touching_trie_node": (2_280_000_000, 4_000_000_000), "read_cached_trie_node": (2_280_000_000, 4_000_000_000),
    "promise_and_base": 1_465_013_400, "promise_and_per_promise": 5_452_176, "promise_return": 560_152_386,
    "validator_stake_base": 911_834_726_400, "validator_total_stake_base": 911_834_726_400,
    "yield_create_base": 153_411_779_276, "yield_create_byte": 15_643_988,
    "yield_create_with_id_base": 290_000_000_000,
    "yield_resume_base": 1_195_627_285_210, "yield_resume_byte": 47_683_715,
}
EXT = {k: (v if isinstance(v, tuple) else (v, v)) for k, v in EXT.items()}

# Action fees: name -> (send_sir, send_not_sir, exec)
FEE = {
    "new_action_receipt": (108_059_500_000, 108_059_500_000, 108_059_500_000),
    "new_data_receipt_base": (36_486_732_312, 36_486_732_312, 36_486_732_312),
    "new_data_receipt_byte": (17_212_011, 47_683_715, 17_212_011),
    "create_account": (500_000_000_000, 500_000_000_000, 7_200_000_000_000),
    "delete_account": (147_489_000_000, 147_489_000_000, 147_489_000_000),
    "deploy_contract": (184_765_750_000, 184_765_750_000, 184_765_750_000),
    "deploy_contract_byte": (6_812_999, 47_683_715, 64_572_944),
    "deploy_global_contract": (184_765_750_000, 184_765_750_000, 184_765_750_000),
    "deploy_global_contract_byte": (6_812_999, 47_683_715, 70_000_000),
    "use_global_contract": (184_765_750_000, 184_765_750_000, 184_765_750_000),
    "use_global_contract_byte": (6_812_999, 47_683_715, 64_572_944),
    "function_call": (200_000_000_000, 200_000_000_000, 780_000_000_000),
    "function_call_byte": (2_235_934, 47_683_715, 2_235_934),
    "transfer": (115_123_062_500, 115_123_062_500, 115_123_062_500),
    "stake": (141_715_687_500, 141_715_687_500, 102_217_625_000),
    "add_full_access_key": (101_765_125_000, 101_765_125_000, 101_765_125_000),
    "add_function_call_key": (102_217_625_000, 102_217_625_000, 102_217_625_000),
    "add_function_call_key_byte": (1_925_331, 47_683_715, 1_925_331),
    "delete_key": (94_946_625_000, 94_946_625_000, 94_946_625_000),
    "deterministic_state_init": (500_000_000_000, 500_000_000_000, 7_430_000_000_000),
    "deterministic_state_init_entry": (0, 0, 200_000_000_000),
    "deterministic_state_init_byte": (72_000_000, 72_000_000, 70_000_000),
    "gas_key_transfer": (115_123_062_500, 115_123_062_500, 235_676_644_250),
    "gas_key_byte": (59_357_464, 59_357_464, 101_435_400),
    "gas_key_nonce_write_base": (0, 0, 64_196_736_000),
}

MAX_REGISTER_SIZE = 104_857_600
MAX_NUMBER_REGISTERS = 100
REGISTERS_MEMORY_LIMIT = 1 << 30
MAX_NUMBER_LOGS = 100
MAX_TOTAL_LOG_LENGTH = 16_384
MAX_KEY_LEN = 2048
MAX_VALUE_LEN = 4 * 1024 * 1024
MAX_CONTRACT_SIZE = 4 * 1024 * 1024
MAX_INPUT_DEPS = 128
MAX_YIELD_PAYLOAD = 1024
MAX_METHOD_NAMES_BYTES = 2000
STORAGE_EXTRA_BYTES_RECORD = 40
LARGE_READ_THRESHOLD = 4000
U128 = (1 << 128) - 1

# Gas-key fee geometry (fitted black-box, see README)
GAS_KEY_INFO_LEN = 18           # borsh length of the gas-key info (send side of add_gas_key_*)
MIN_GAS_KEY_VALUE_LEN = 27      # estimated access-key value length (exec side of transfer_to_gas_key)
NONCE_INDEX_LEN = 2
NONCE_VALUE_LEN = 8


def debug_str(s):
    """Rust `{:?}` of a str (without the quotes)."""
    out = []
    for ch in s:
        o = ord(ch)
        if ch == "\t":
            out.append("\\t")
        elif ch == "\r":
            out.append("\\r")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\\":
            out.append("\\\\")
        elif ch == '"':
            out.append('\\"')
        elif ch == "\0":
            out.append("\\0")
        elif (ch != " " and not ch.isprintable()) or unicodedata.category(ch) in ("Mn", "Me") \
                or 0xE000 <= o <= 0xF8FF:
            out.append("\\u{%x}" % o)
        else:
            out.append(ch)
    return "".join(out)


class Ctx:
    """The harness context (src/main.rs `context`) plus per-case options."""

    def __init__(self, tok):
        self.receivers = []
        self.input = b""
        self.results = []
        self.deposit = 0
        self.balance = BALANCE
        if tok is None or tok == "":
            return
        if "=" not in tok:
            self.receivers = [a.encode() for a in tok.split(",")]
            return
        for kv in tok.split(";"):
            if not kv:
                continue
            k, v = kv.split("=", 1)
            if k == "rcv":
                self.receivers = [a.encode() for a in v.split(",") if a]
            elif k == "input":
                self.input = bytes.fromhex(v)
            elif k == "results":
                for r in v.split(","):
                    if not r:
                        continue
                    if r[0] == "S":
                        self.results.append(("S", bytes.fromhex(r[1:])))
                    elif r[0] == "F":
                        self.results.append(("F", None))
                    else:
                        self.results.append(("N", None))
            elif k == "deposit":
                self.deposit = int(v)
            elif k == "balance":
                self.balance = int(v)
            else:
                raise ValueError(f"unknown option {k}")


# ---- charging

def pay(inst, key, n=None):
    gc = inst.gc
    g = EXT[key][0]
    if n is None:
        x = g
    else:
        x = g * n
        if x > U64:
            raise HostErr("IntegerOverflow")
    before = gc.burnt
    try:
        gc.burn(x)
    finally:
        inst.prof[key] = inst.prof.get(key, 0) + gc.burnt - before


def deduct(inst, burn, use):
    """Action-fee path (deduct_gas), profiled as action gas."""
    gc = inst.gc
    if burn > U64 or use > U64:
        raise HostErr("IntegerOverflow")
    before = gc.burnt
    try:
        gc.deduct(burn, use)
    finally:
        d = gc.burnt - before
        inst.act_gas += d
        inst.send_compute += d


def act(inst, fee, sir, n=1, exec_n=None):
    f = FEE[fee]
    if exec_n is None:
        exec_n = n
    s = (f[0] if sir else f[1]) * n
    e = f[2] * exec_n
    if s > U64 or e > U64 or s + e > U64:
        raise HostErr("IntegerOverflow")
    deduct(inst, s, s + e)


def prepay(inst, gas):
    deduct(inst, 0, gas)


def compute_usage(inst):
    gc = inst.gc
    host = 0
    comp = 0
    for k, v in inst.prof.items():
        host += v
        g, c = EXT[k]
        comp += v * c // g
    wasm = gc.burnt - inst.act_gas - host
    return comp + inst.send_compute + wasm


# ---- guest memory and registers

def mem_read(inst, ptr, n):
    pay(inst, "read_memory_base")
    pay(inst, "read_memory_byte", n)
    end = ptr + n
    if end > inst.memlen:
        raise HostErr("MemoryAccessViolation")
    return bytes(inst.mem[ptr:end])


def mem_write(inst, ptr, data):
    pay(inst, "write_memory_base")
    pay(inst, "write_memory_byte", len(data))
    end = ptr + len(data)
    if end > inst.memlen:
        raise HostErr("MemoryAccessViolation")
    inst.mem[ptr:end] = data


def reg_read(inst, rid):
    data = inst.regs.get(rid)
    if data is None:
        raise HostErr(f"InvalidRegisterId {{ register_id: {rid} }}")
    pay(inst, "read_register_base")
    pay(inst, "read_register_byte", len(data))
    return data


def reg_set(inst, rid, data, rc=False):
    pay(inst, "write_register_base")
    if not rc:
        pay(inst, "write_register_byte", len(data))
    n = len(data)
    if n > MAX_REGISTER_SIZE:
        raise HostErr("MemoryAccessViolation")
    if len(inst.regs) >= MAX_NUMBER_REGISTERS:
        raise HostErr("MemoryAccessViolation")
    old = inst.regs.get(rid)
    usage = inst.reg_usage - (len(old) + 8 if old is not None else 0) + n + 8
    if usage > REGISTERS_MEMORY_LIMIT:
        raise HostErr("MemoryAccessViolation")
    inst.regs[rid] = data
    inst.reg_usage = usage


def gmr(inst, ptr, n):
    if n == U64:
        return reg_read(inst, ptr)
    return mem_read(inst, ptr, n)


def read_u128(inst, ptr):
    return int.from_bytes(mem_read(inst, ptr, 16), "little")


def read_account_id(inst, n, ptr):
    data = gmr(inst, ptr, n)
    pay(inst, "utf8_decoding_base")
    pay(inst, "utf8_decoding_byte", len(data))
    try:
        s = data.decode("utf-8")
    except UnicodeDecodeError:
        raise HostErr("BadUTF8")
    if not valid_account_id(s):
        raise HostErr("InvalidAccountId")
    return data


def get_utf8(inst, n, ptr):
    pay(inst, "utf8_decoding_base")
    max_len = max(0, MAX_TOTAL_LOG_LENGTH - inst.total_log)
    if n != U64:
        if n > max_len:
            raise HostErr(f"TotalLogLengthExceeded {{ length: {inst.total_log + n}, limit: {MAX_TOTAL_LOG_LENGTH} }}")
        buf = mem_read(inst, ptr, n)
    else:
        buf = bytearray()
        i = 0
        while True:
            pay(inst, "read_memory_base")
            pay(inst, "read_memory_byte", 1)
            if ptr + i + 1 > inst.memlen:
                raise HostErr("MemoryAccessViolation")
            b = inst.mem[ptr + i]
            if b == 0:
                break
            if i == max_len:
                raise HostErr(f"TotalLogLengthExceeded {{ length: {inst.total_log + max_len + 1}, "
                              f"limit: {MAX_TOTAL_LOG_LENGTH} }}")
            buf.append(b)
            i += 1
        buf = bytes(buf)
    pay(inst, "utf8_decoding_byte", len(buf))
    try:
        return buf.decode("utf-8")
    except UnicodeDecodeError:
        raise HostErr("BadUTF8")


def get_utf16(inst, n, ptr):
    pay(inst, "utf16_decoding_base")
    max_len = max(0, MAX_TOTAL_LOG_LENGTH - inst.total_log)
    if n != U64:
        # unlike UTF-8, the explicit-length path reads memory before the log-length check
        buf = mem_read(inst, ptr, n)
        # odd length is checked before the log-length limit (black-box probe: log_utf16(16385, 0)
        # -> BadUTF16; README H6 note)
        if n % 2:
            raise HostErr("BadUTF16")
        if n > max_len:
            raise HostErr(f"TotalLogLengthExceeded {{ length: {inst.total_log + n}, limit: {MAX_TOTAL_LOG_LENGTH} }}")
    else:
        buf = bytearray()
        i = 0
        while True:
            pay(inst, "read_memory_base")
            pay(inst, "read_memory_byte", 2)
            if ptr + i + 2 > inst.memlen:
                raise HostErr("MemoryAccessViolation")
            u = inst.mem[ptr + i] | inst.mem[ptr + i + 1] << 8
            if u == 0:
                break
            if i + 2 > max_len:
                raise HostErr(f"TotalLogLengthExceeded {{ length: {inst.total_log + i + 2}, "
                              f"limit: {MAX_TOTAL_LOG_LENGTH} }}")
            buf += bytes([u & 0xFF, u >> 8])
            i += 2
        buf = bytes(buf)
    pay(inst, "utf16_decoding_byte", len(buf))
    try:
        return buf.decode("utf-16-le")
    except UnicodeDecodeError:
        raise HostErr("BadUTF16")


def check_logs_count(inst):
    if len(inst.logs) >= MAX_NUMBER_LOGS:
        raise HostErr(f"NumberOfLogsExceeded {{ limit: {MAX_NUMBER_LOGS} }}")


def push_log(inst, s, prefix=b""):
    """Charge log_base + log_byte per byte of `s`, then record `prefix + s`.  The limit check is on the
    recorded length L; on failure nearcore reports total + 2L (the length is added twice)."""
    b = s.encode("utf-8")
    pay(inst, "log_base")
    pay(inst, "log_byte", len(b))
    rec = prefix + b
    if inst.total_log + len(rec) > MAX_TOTAL_LOG_LENGTH:
        raise HostErr(f"TotalLogLengthExceeded {{ length: {inst.total_log + 2 * len(rec)}, "
                      f"limit: {MAX_TOTAL_LOG_LENGTH} }}")
    inst.total_log += len(rec)
    inst.logs.append(rec)


# ---- public keys, account types

def parse_pk(data):
    """borsh PublicKey -> canonical bytes, or None."""
    if len(data) == 33 and data[0] == 0:
        return data
    if len(data) == 65 and data[0] == 1:
        return data
    if len(data) == 1953 and data[0] == 2:      # ML-DSA-65
        return data
    return None


def account_type(acc):
    hexd = set(b"0123456789abcdef")
    if len(acc) == 64 and all(c in hexd for c in acc):
        return "near"
    if len(acc) == 42 and acc[:2] == b"0x" and all(c in hexd for c in acc[2:]):
        return "eth"
    if len(acc) == 42 and acc[:2] == b"0s" and all(c in hexd for c in acc[2:]):
        return "det"
    return "named"


# ---- promises / receipts (MockedExternal semantics)

def push_promise(inst, p):
    if len(inst.promises) >= MAX_PROMISES:
        raise HostErr(f"NumberPromisesExceeded {{ number_of_promises: {len(inst.promises) + 1}, "
                      f"limit: {MAX_PROMISES} }}")
    inst.promises.append(p)
    return len(inst.promises) - 1


def get_promise(inst, idx):
    if idx >= len(inst.promises):
        raise HostErr(f"InvalidPromiseIndex {{ promise_idx: {idx} }}")
    return inst.promises[idx]


def single_receipt(inst, idx):
    p = get_promise(inst, idx)
    if p[0] != "R":
        raise HostErr("CannotAppendActionToJointPromise")
    r = p[1]
    return r, inst.rcpt_recv[r] == CURRENT_ACCOUNT


def new_data_id(inst):
    d = hashlib.sha256(inst.data_counter.to_bytes(8, "little")).digest()
    inst.data_counter += 1
    return d


def pay_new_receipt(inst, sir, deps):
    f = FEE["new_action_receipt"]
    burn = f[0] if sir else f[1]
    use = f[2]
    db = FEE["new_data_receipt_base"]
    for dsir in deps:
        burn += (db[0] if dsir else db[1]) + db[2]
    deduct(inst, burn, use + burn)


def create_receipt(inst, deps, acc):
    r = len(inst.alog)
    inst.alog.append(f"CR({','.join(str(d) for d in deps)})>{acc.decode()}")
    inst.rcpt_recv[r] = acc
    return r


def deduct_balance(inst, amount):
    if amount > inst.balance:
        raise HostErr("BalanceExceeded")
    inst.balance -= amount


def append_action(inst, r, kind, text):
    """MockedExternal: an action's index is its position in the action log."""
    inst.alog.append(text)
    i = len(inst.alog) - 1
    inst.actions[i] = [kind, r, {}]
    return i


def function_call(inst, idx, mlen, mptr, alen, aptr, amt_ptr, gas, weight):
    pay(inst, "base")
    amount = read_u128(inst, amt_ptr)
    method = gmr(inst, mptr, mlen)
    if not method:
        raise HostErr("EmptyMethodName")
    args = gmr(inst, aptr, alen)
    r, sir = single_receipt(inst, idx)
    act(inst, "function_call", sir)
    act(inst, "function_call_byte", sir, len(method) + len(args))
    prepay(inst, gas)
    if amount == 1 and inst.balance == 0:
        pass        # one-yocto exemption
    else:
        deduct_balance(inst, amount)
    append_action(inst, r, "FC", f"FC@{r}:{method.hex()}:{args.hex()}:{amount}:{gas}:{weight}")


def batch_create(inst, n, ptr):
    pay(inst, "base")
    acc = read_account_id(inst, n, ptr)
    pay_new_receipt(inst, acc == CURRENT_ACCOUNT, [])
    r = create_receipt(inst, [], acc)       # the receipt exists before the promise-count check
    return push_promise(inst, ("R", r))


def batch_then(inst, idx, n, ptr):
    pay(inst, "base")
    acc = read_account_id(inst, n, ptr)
    p = get_promise(inst, idx)
    deps = [p[1]] if p[0] == "R" else list(p[1])
    pay_new_receipt(inst, acc == CURRENT_ACCOUNT, [inst.rcpt_recv[d] == CURRENT_ACCOUNT for d in deps])
    r = create_receipt(inst, deps, acc)
    return push_promise(inst, ("R", r))


def h_promise_and(inst, ptr, count):
    pay(inst, "base")
    pay(inst, "promise_and_base")
    nb = count * 8
    if nb > U64:
        raise HostErr("IntegerOverflow")
    pay(inst, "promise_and_per_promise", nb)
    data = mem_read(inst, ptr, nb)
    deps = []
    for i in range(count):
        idx = int.from_bytes(data[8 * i:8 * i + 8], "little")
        p = get_promise(inst, idx)
        if p[0] == "R":
            deps.append(p[1])
        else:
            deps.extend(p[1])
    if len(deps) > MAX_INPUT_DEPS:
        raise HostErr(f"NumberInputDataDependenciesExceeded {{ number_of_input_data_dependencies: {len(deps)}, "
                      f"limit: {MAX_INPUT_DEPS} }}")
    return push_promise(inst, ("J", deps))


def split_method_names(data):
    """Comma-split on bytes; an empty name is EmptyMethodName.  MockedExternal does not check UTF-8 (the
    production receipt manager would raise InvalidMethodName later, after the fees)."""
    if not data:
        return []
    out = data.split(b",")
    if any(not nm for nm in out):
        raise HostErr("EmptyMethodName")
    return out


def add_fc_key(inst, idx, pk_len, pk_ptr, nonce, allow_ptr, rlen, rptr, nlen, nptr, gas_key):
    pay(inst, "base")
    pkd = gmr(inst, pk_ptr, pk_len)
    if gas_key and nonce > 0xFFFF:
        raise HostErr("IntegerOverflow")
    pk = parse_pk(pkd)
    allowance = read_u128(inst, allow_ptr)
    recv = read_account_id(inst, rlen, rptr)
    names_raw = gmr(inst, nptr, nlen)
    names = split_method_names(names_raw)
    r, sir = single_receipt(inst, idx)
    nbytes = sum(len(x) + 1 for x in names)
    act(inst, "add_function_call_key", sir)
    act(inst, "add_function_call_key_byte", sir, nbytes)
    if gas_key:
        gas_key_add_fees(inst, r, sir, 0 if pk is None else len(pk), nonce)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    if gas_key:
        append_action(inst, r, "GK", "OTHER")
        return
    al = "-" if allowance == 0 else str(allowance)
    append_action(inst, r, "AC", f"AC@{r}:{pk.hex()}:{nonce}:{al}:{recv.decode()}:"
                                 f"{'/'.join(x.hex() for x in names)}")


def gas_key_add_fees(inst, r, sir, pk_len, num_nonces):
    acc_len = len(inst.rcpt_recv[r])
    f = FEE["gas_key_nonce_write_base"]
    deduct(inst, 0, f[2] * num_nonces)
    f = FEE["gas_key_byte"]
    s = (f[0] if sir else f[1]) * GAS_KEY_INFO_LEN
    key_len = 1 + acc_len + 1 + pk_len + NONCE_INDEX_LEN
    e = f[2] * (key_len + NONCE_VALUE_LEN) * num_nonces
    if s + e > U64:
        raise HostErr("IntegerOverflow")
    deduct(inst, s, s + e)


def yield_create(inst, with_id, a):
    pay(inst, "base")
    if with_id:
        mlen, mptr, alen, aptr, amt_ptr, gas, weight, ylen, yptr = a
        pay(inst, "yield_create_with_id_base")
        amount = read_u128(inst, amt_ptr)
    else:
        mlen, mptr, alen, aptr, gas, weight, reg = a
        pay(inst, "yield_create_base")
        amount = 0
    method = gmr(inst, mptr, mlen)
    if not method:
        raise HostErr("EmptyMethodName")
    args = gmr(inst, aptr, alen)
    yid = None
    if with_id:
        yid = gmr(inst, yptr, ylen)
        if len(yid) != 32:
            raise HostErr("YieldIdMalformed")
    pay(inst, "yield_create_byte", len(method) + len(args))
    if with_id:
        # the yield receipt is created (or found pending) before any receipt fee is charged
        if yid in inst.yields_by_id:
            return U64
        r = new_yield_receipt(inst, yid)
    prepay(inst, gas)
    pay_new_receipt(inst, True, [True])
    if not with_id:
        r = new_yield_receipt(inst, None)
    pidx = push_promise(inst, ("R", r))
    act(inst, "function_call", True)
    act(inst, "function_call_byte", True, len(method) + len(args))
    if with_id:
        if amount == 1 and inst.balance == 0:
            pass
        else:
            deduct_balance(inst, amount)
    append_action(inst, r, "FC", f"FC@{r}:{method.hex()}:{args.hex()}:{amount}:{gas}:{weight}")
    if not with_id:
        reg_set(inst, reg, inst.yield_data[r])
    return pidx


def new_yield_receipt(inst, yid):
    data_id = new_data_id(inst)
    r = len(inst.alog)
    inst.alog.append(f"YC:{data_id.hex()}>{CURRENT_ACCOUNT.decode()}:{yid.hex() if yid is not None else '-'}")
    inst.rcpt_recv[r] = CURRENT_ACCOUNT
    inst.yields.add(data_id)
    inst.yield_data[r] = data_id
    if yid is not None:
        inst.yields_by_id[yid] = data_id
    return r


def yield_resume(inst, with_id, a):
    ilen, iptr, plen, pptr = a
    pay(inst, "base")
    pay(inst, "yield_resume_base")
    pay(inst, "yield_resume_byte", plen)
    ident = gmr(inst, iptr, ilen)
    payload = gmr(inst, pptr, plen)
    if len(payload) > MAX_YIELD_PAYLOAD:
        raise HostErr(f"YieldPayloadLength {{ length: {len(payload)}, limit: {MAX_YIELD_PAYLOAD} }}")
    if len(ident) != 32:
        raise HostErr("YieldIdMalformed" if with_id else "DataIdMalformed")
    if with_id:
        data_id = inst.yields_by_id.get(ident)
        if data_id is None:
            return 0
    else:
        data_id = ident
    inst.alog.append(f"YR:{data_id.hex()}:{payload.hex()}")
    return 1 if data_id in inst.yields else 0


TRACE = False


def host_call(inst, f, args):
    gc = inst.gc
    # sync before the call
    gc.burnt = gc.prepaid - gc.promises - inst.g
    if TRACE:
        sys.stderr.write(f"  {f.imp_name}{tuple(args)} burnt={gc.burnt} used={gc.burnt + gc.promises}\n")
    try:
        res = host_dispatch(inst, f.imp_name, args)
    except Exception as e:
        e.synced = True
        inst.g = gc.remaining()
        raise
    inst.g = gc.remaining()
    return res


OOD_HOSTS = {"ecrecover", "p256_verify", "alt_bn128_g1_multiexp", "alt_bn128_g1_sum", "alt_bn128_pairing_check",
             "bls12381_p1_sum", "bls12381_p2_sum", "bls12381_g1_multiexp", "bls12381_g2_multiexp",
             "bls12381_map_fp_to_g1", "bls12381_map_fp2_to_g2", "bls12381_pairing_check",
             "bls12381_p1_decompress", "bls12381_p2_decompress"}


def host_dispatch(inst, name, a):
    h = HANDLERS.get(name)
    if h is None:
        if name in OOD_HOSTS:
            raise OutOfDomain(f"curve host function {name}")
        raise Unmodeled(f"host function {name}")
    return h(inst, *a)


# ---- individual host functions

def h_value_return(inst, n, ptr):
    pay(inst, "base")
    data = gmr(inst, ptr, n)
    if len(data) > MAX_RETURNED_DATA:
        raise HostErr(f"ReturnedValueLengthExceeded {{ length: {len(data)}, limit: {MAX_RETURNED_DATA} }}")
    burn = 0
    f = FEE["new_data_receipt_byte"]
    for rcv in inst.ctx.receivers:
        sir = rcv == CURRENT_ACCOUNT
        burn += ((f[0] if sir else f[1]) + f[2]) * len(data)
    deduct(inst, burn, burn)
    inst.ret = data


def h_panic(inst):
    pay(inst, "base")
    raise HostErr('GuestPanic { panic_msg: "explicit guest panic" }')


def h_panic_utf8(inst, n, ptr):
    pay(inst, "base")
    s = get_utf8(inst, n, ptr)
    raise HostErr(f'GuestPanic {{ panic_msg: "{debug_str(s)}" }}')


def h_log_utf8(inst, n, ptr):
    pay(inst, "base")
    check_logs_count(inst)
    s = get_utf8(inst, n, ptr)
    push_log(inst, s)


def h_log_utf16(inst, n, ptr):
    pay(inst, "base")
    check_logs_count(inst)
    s = get_utf16(inst, n, ptr)
    push_log(inst, s)


def h_abort(inst, msg_ptr, file_ptr, line, col):
    pay(inst, "base")
    if msg_ptr < 4 or file_ptr < 4:
        raise HostErr("BadUTF16")
    check_logs_count(inst)
    mlen = int.from_bytes(mem_read(inst, msg_ptr - 4, 4), "little")
    flen = int.from_bytes(mem_read(inst, file_ptr - 4, 4), "little")
    msg = get_utf16(inst, mlen, msg_ptr)
    fname = get_utf16(inst, flen, file_ptr)
    message = f'{msg}, filename: "{fname}" line: {line} col: {col}'
    push_log(inst, message, b"ABORT: ")
    raise HostErr(f'GuestPanic {{ panic_msg: "{debug_str(message)}" }}')


def h_gas(inst, opcodes):
    inst.gc.pay_per(R, opcodes)


def h_read_register(inst, rid, ptr):
    pay(inst, "base")
    data = reg_read(inst, rid)
    mem_write(inst, ptr, data)


def h_register_len(inst, rid):
    pay(inst, "base")
    d = inst.regs.get(rid)
    return U64 if d is None else len(d)


def h_write_register(inst, rid, n, ptr):
    pay(inst, "base")
    data = mem_read(inst, ptr, n)
    reg_set(inst, rid, data)


def _reg_const(val, rc=False):
    def h(inst, rid):
        pay(inst, "base")
        reg_set(inst, rid, val(inst), rc)
    return h


def _ret_const(val):
    def h(inst):
        pay(inst, "base")
        return val(inst)
    return h


def _hash(name, fn):
    def h(inst, n, ptr, rid):
        pay(inst, name + "_base")
        data = gmr(inst, ptr, n)
        pay(inst, name + "_byte", len(data))
        reg_set(inst, rid, fn(data))
    return h


def h_ripemd160(inst, n, ptr, rid):
    pay(inst, "ripemd160_base")
    data = gmr(inst, ptr, n)
    pay(inst, "ripemd160_block", (len(data) + 8) // 64 + 1)
    reg_set(inst, rid, nearcrypto.ripemd160(data))


def h_ed25519_verify(inst, slen, sptr, mlen, mptr, plen, pptr):
    pay(inst, "ed25519_verify_base")
    sig = gmr(inst, sptr, slen)
    if len(sig) != 64:
        raise HostErr('Ed25519VerifyInvalidInput { msg: "invalid signature length" }')
    if sig[63] & 0xE0:
        return 0
    msg = gmr(inst, mptr, mlen)
    pay(inst, "ed25519_verify_byte", len(msg))
    pk = gmr(inst, pptr, plen)
    if len(pk) != 32:
        raise HostErr('Ed25519VerifyInvalidInput { msg: "invalid public key length" }')
    return 1 if nearcrypto.ed25519_verify(sig, msg, pk) else 0


def _mem_u128(val):
    def h(inst, ptr):
        pay(inst, "base")
        mem_write(inst, ptr, val(inst).to_bytes(16, "little"))
    return h


def h_promise_create(inst, alen, aptr, mlen, mptr, glen, gptr, amt, gas):
    idx = batch_create(inst, alen, aptr)
    function_call(inst, idx, mlen, mptr, glen, gptr, amt, gas, 0)
    return idx


def h_promise_then(inst, pidx, alen, aptr, mlen, mptr, glen, gptr, amt, gas):
    idx = batch_then(inst, pidx, alen, aptr)
    function_call(inst, idx, mlen, mptr, glen, gptr, amt, gas, 0)
    return idx


def h_set_refund_to(inst, idx, n, ptr):
    pay(inst, "base")
    acc = read_account_id(inst, n, ptr)
    p = get_promise(inst, idx)
    if p[0] != "R":
        raise HostErr("CannotSetRefundToOnJointPromise")
    inst.alog.append(f"RT@{p[1]}:{acc.decode()}")


def h_promise_return(inst, idx):
    pay(inst, "base")
    pay(inst, "promise_return")
    p = get_promise(inst, idx)
    if p[0] != "R":
        raise HostErr("CannotReturnJointPromise")
    inst.ret = ("receipt", p[1])


def h_create_account(inst, idx):
    pay(inst, "base")
    r, sir = single_receipt(inst, idx)
    act(inst, "create_account", sir)
    append_action(inst, r, "CA", f"CA@{r}")


def _deploy(fee, glob):
    def h(inst, idx, n, ptr):
        pay(inst, "base")
        code = gmr(inst, ptr, n)
        if len(code) > MAX_CONTRACT_SIZE:
            raise HostErr(f"ContractSizeExceeded {{ size: {len(code)}, limit: {MAX_CONTRACT_SIZE} }}")
        r, sir = single_receipt(inst, idx)
        act(inst, fee, sir)
        act(inst, fee + "_byte", sir, len(code))
        append_action(inst, r, "DC", "OTHER" if glob else f"DC@{r}:{code.hex()}")
    return h


def h_use_global(inst, idx, n, ptr):
    pay(inst, "base")
    h = gmr(inst, ptr, n)
    if len(h) != 32:
        raise HostErr("ContractCodeHashMalformed")
    r, sir = single_receipt(inst, idx)
    act(inst, "use_global_contract", sir)
    act(inst, "use_global_contract_byte", sir, 32)
    append_action(inst, r, "UG", "OTHER")


def h_use_global_by_account(inst, idx, n, ptr):
    pay(inst, "base")
    acc = read_account_id(inst, n, ptr)
    r, sir = single_receipt(inst, idx)
    act(inst, "use_global_contract", sir)
    act(inst, "use_global_contract_byte", sir, len(acc))
    append_action(inst, r, "UG", "OTHER")


def _state_init(by_account):
    def h(inst, idx, n, ptr, amt_ptr):
        pay(inst, "base")
        if by_account:
            read_account_id(inst, n, ptr)
        else:
            hsh = gmr(inst, ptr, n)
            if len(hsh) != 32:
                raise HostErr("ContractCodeHashMalformed")
        amount = read_u128(inst, amt_ptr)
        r, sir = single_receipt(inst, idx)
        act(inst, "deterministic_state_init", sir)
        deduct_balance(inst, amount)
        return append_action(inst, r, "SI", "OTHER")
    return h


def h_set_state_init_entry(inst, idx, aidx, klen, kptr, vlen, vptr):
    pay(inst, "base")
    r, sir = single_receipt(inst, idx)
    k = gmr(inst, kptr, klen)
    v = gmr(inst, vptr, vlen)
    act(inst, "deterministic_state_init_entry", sir)
    act(inst, "deterministic_state_init_byte", sir, len(k) + len(v))
    a = inst.actions.get(aidx)
    if a is None or a[0] != "SI" or a[1] != r:
        raise HostErr(f"InvalidActionIndex {{ receipt_index: {r}, action_index: {aidx} }}")
    if k in a[2]:
        raise HostErr("DataEntryAlreadyExists")
    a[2][k] = v


def h_fc(inst, idx, mlen, mptr, alen, aptr, amt, gas):
    function_call(inst, idx, mlen, mptr, alen, aptr, amt, gas, 0)


def h_fc_weight(inst, idx, mlen, mptr, alen, aptr, amt, gas, w):
    function_call(inst, idx, mlen, mptr, alen, aptr, amt, gas, w)


def h_transfer(inst, idx, amt_ptr):
    pay(inst, "base")
    amount = read_u128(inst, amt_ptr)
    r, sir = single_receipt(inst, idx)
    t = account_type(inst.rcpt_recv[r])
    # implicit-account surcharges are folded into the one transfer fee
    fees = ["transfer"] + (["create_account"] if t != "named" else []) + (["add_full_access_key"] if t == "near" else [])
    s_ = sum(FEE[f][0] if sir else FEE[f][1] for f in fees)
    e_ = sum(FEE[f][2] for f in fees)
    deduct(inst, s_, s_ + e_)
    deduct_balance(inst, amount)
    append_action(inst, r, "TR", f"TR@{r}:{amount}")


def h_stake(inst, idx, amt_ptr, pk_len, pk_ptr):
    pay(inst, "base")
    amount = read_u128(inst, amt_ptr)
    pk = parse_pk(gmr(inst, pk_ptr, pk_len))
    r, sir = single_receipt(inst, idx)
    act(inst, "stake", sir)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    append_action(inst, r, "ST", f"ST@{r}:{amount}:{pk.hex()}")


def h_add_full_key(inst, idx, pk_len, pk_ptr, nonce):
    pay(inst, "base")
    pk = parse_pk(gmr(inst, pk_ptr, pk_len))
    r, sir = single_receipt(inst, idx)
    act(inst, "add_full_access_key", sir)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    append_action(inst, r, "AF", f"AF@{r}:{pk.hex()}:{nonce}")


def h_add_fc_key(inst, idx, pk_len, pk_ptr, nonce, allow_ptr, rlen, rptr, nlen, nptr):
    add_fc_key(inst, idx, pk_len, pk_ptr, nonce, allow_ptr, rlen, rptr, nlen, nptr, False)


def h_add_gas_fc_key(inst, idx, pk_len, pk_ptr, nn, allow_ptr, rlen, rptr, nlen, nptr):
    add_fc_key(inst, idx, pk_len, pk_ptr, nn, allow_ptr, rlen, rptr, nlen, nptr, True)


def h_delete_key(inst, idx, pk_len, pk_ptr):
    pay(inst, "base")
    pk = parse_pk(gmr(inst, pk_ptr, pk_len))
    r, sir = single_receipt(inst, idx)
    act(inst, "delete_key", sir)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    append_action(inst, r, "DK", f"DK@{r}:{pk.hex()}")


def h_delete_account(inst, idx, n, ptr):
    pay(inst, "base")
    acc = read_account_id(inst, n, ptr)
    r, sir = single_receipt(inst, idx)
    act(inst, "delete_account", sir)
    append_action(inst, r, "DA", f"DA@{r}:{acc.decode()}")


def h_transfer_to_gas_key(inst, idx, pk_len, pk_ptr, amt_ptr):
    pay(inst, "base")
    pkd = gmr(inst, pk_ptr, pk_len)
    amount = read_u128(inst, amt_ptr)
    r, sir = single_receipt(inst, idx)
    acc_len = len(inst.rcpt_recv[r])
    act(inst, "gas_key_transfer", sir)
    pk = parse_pk(pkd)
    pk_len = 0 if pk is None else len(pk)       # an undecodable key is charged as length 0
    f = FEE["gas_key_byte"]
    s = (f[0] if sir else f[1]) * pk_len
    e = f[2] * (1 + acc_len + 1 + pk_len + MIN_GAS_KEY_VALUE_LEN)
    deduct(inst, s, s + e)
    deduct_balance(inst, amount)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    append_action(inst, r, "TG", "OTHER")


def h_add_gas_full_key(inst, idx, pk_len, pk_ptr, nn):
    pay(inst, "base")
    pkd = gmr(inst, pk_ptr, pk_len)
    if nn > 0xFFFF:
        raise HostErr("IntegerOverflow")
    pk = parse_pk(pkd)
    r, sir = single_receipt(inst, idx)
    act(inst, "add_full_access_key", sir)
    gas_key_add_fees(inst, r, sir, 0 if pk is None else len(pk), nn)
    if pk is None:
        raise HostErr("InvalidPublicKey")
    append_action(inst, r, "GK", "OTHER")


def h_results_count(inst):
    pay(inst, "base")
    return len(inst.ctx.results)


def h_promise_result(inst, idx, rid):
    pay(inst, "base")
    if idx >= len(inst.ctx.results):
        raise HostErr(f"InvalidPromiseResultIndex {{ result_idx: {idx} }}")
    k, v = inst.ctx.results[idx]
    if k == "N":
        return 0
    if k == "F":
        return 2
    reg_set(inst, rid, v, rc=True)
    return 1


def check_key(n):
    if n > MAX_KEY_LEN:
        raise HostErr(f"KeyLengthExceeded {{ length: {n}, limit: {MAX_KEY_LEN} }}")


def h_storage_write(inst, klen, kptr, vlen, vptr, rid):
    pay(inst, "base")
    pay(inst, "storage_write_base")
    k = gmr(inst, kptr, klen)
    check_key(len(k))
    v = gmr(inst, vptr, vlen)
    if len(v) > MAX_VALUE_LEN:
        raise HostErr(f"ValueLengthExceeded {{ length: {len(v)}, limit: {MAX_VALUE_LEN} }}")
    pay(inst, "storage_write_key_byte", len(k))
    pay(inst, "storage_write_value_byte", len(v))
    old = inst.store.write(inst, k, v)
    if old is not None:
        inst.storage_usage += len(v) - len(old)
        reg_set(inst, rid, old)
        return 1
    inst.storage_usage += len(k) + len(v) + STORAGE_EXTRA_BYTES_RECORD
    return 0


def h_storage_read(inst, klen, kptr, rid):
    pay(inst, "base")
    pay(inst, "storage_read_base")
    k = gmr(inst, kptr, klen)
    check_key(len(k))
    pay(inst, "storage_read_key_byte", len(k))
    v = inst.store.read(inst, k)
    if v is None:
        return 0
    reg_set(inst, rid, v)
    return 1


def h_storage_remove(inst, klen, kptr, rid):
    pay(inst, "base")
    pay(inst, "storage_remove_base")
    k = gmr(inst, kptr, klen)
    check_key(len(k))
    pay(inst, "storage_remove_key_byte", len(k))
    old = inst.store.remove(inst, k)
    if old is None:
        return 0
    inst.storage_usage -= len(k) + len(old) + STORAGE_EXTRA_BYTES_RECORD
    reg_set(inst, rid, old)
    return 1


def h_storage_has_key(inst, klen, kptr):
    pay(inst, "base")
    pay(inst, "storage_has_key_base")
    k = gmr(inst, kptr, klen)
    check_key(len(k))
    pay(inst, "storage_has_key_byte", len(k))
    return 1 if inst.store.has(inst, k) else 0


def _deprecated(name):
    def h(inst, *a):
        raise HostErr(f'Deprecated {{ method_name: "{name}" }}')
    return h


def h_validator_stake(inst, n, ptr, out):
    pay(inst, "base")
    read_account_id(inst, n, ptr)
    pay(inst, "validator_stake_base")
    mem_write(inst, out, bytes(16))


def h_validator_total(inst, out):
    pay(inst, "base")
    pay(inst, "validator_total_stake_base")
    mem_write(inst, out, bytes(16))


HANDLERS = {
    "value_return": h_value_return, "panic": h_panic, "panic_utf8": h_panic_utf8, "log_utf8": h_log_utf8,
    "log_utf16": h_log_utf16, "abort": h_abort, "gas": h_gas,
    "read_register": h_read_register, "register_len": h_register_len, "write_register": h_write_register,
    "current_account_id": _reg_const(lambda i: CURRENT_ACCOUNT),
    "chain_id": _reg_const(lambda i: b"test"),
    "signer_account_id": _reg_const(lambda i: b"bob.near"),
    "signer_account_pk": _reg_const(lambda i: bytes([0, 1, 2])),
    "predecessor_account_id": _reg_const(lambda i: b"bob.near"),
    "refund_to_account_id": _reg_const(lambda i: b"bob.near"),
    "input": _reg_const(lambda i: i.ctx.input, rc=True),
    "random_seed": _reg_const(lambda i: bytes(32)),
    "block_index": _ret_const(lambda i: 10), "block_timestamp": _ret_const(lambda i: 42),
    "epoch_height": _ret_const(lambda i: 1), "storage_usage": _ret_const(lambda i: i.storage_usage),
    "prepaid_gas": _ret_const(lambda i: i.gc.prepaid),
    "used_gas": _ret_const(lambda i: i.gc.burnt + i.gc.promises),
    "current_contract_code": lambda inst, rid: _ret_const(lambda i: 0)(inst),
    "account_balance": _mem_u128(lambda i: i.balance),
    "account_locked_balance": _mem_u128(lambda i: 0),
    "attached_deposit": _mem_u128(lambda i: i.ctx.deposit),
    "sha256": _hash("sha256", nearcrypto.sha256), "keccak256": _hash("keccak256", nearcrypto.keccak256),
    "keccak512": _hash("keccak512", nearcrypto.keccak512), "ripemd160": h_ripemd160,
    "ed25519_verify": h_ed25519_verify,
    "promise_create": h_promise_create, "promise_then": h_promise_then, "promise_and": h_promise_and,
    "promise_batch_create": lambda inst, n, p: batch_create(inst, n, p),
    "promise_batch_then": lambda inst, i, n, p: batch_then(inst, i, n, p),
    "promise_set_refund_to": h_set_refund_to, "promise_return": h_promise_return,
    "promise_batch_action_create_account": h_create_account,
    "promise_batch_action_deploy_contract": _deploy("deploy_contract", False),
    "promise_batch_action_deploy_global_contract": _deploy("deploy_global_contract", True),
    "promise_batch_action_deploy_global_contract_by_account_id": _deploy("deploy_global_contract", True),
    "promise_batch_action_use_global_contract": h_use_global,
    "promise_batch_action_use_global_contract_by_account_id": h_use_global_by_account,
    "promise_batch_action_state_init": _state_init(False),
    "promise_batch_action_state_init_by_account_id": _state_init(True),
    "set_state_init_data_entry": h_set_state_init_entry,
    "promise_batch_action_function_call": h_fc, "promise_batch_action_function_call_weight": h_fc_weight,
    "promise_batch_action_transfer": h_transfer, "promise_batch_action_stake": h_stake,
    "promise_batch_action_add_key_with_full_access": h_add_full_key,
    "promise_batch_action_add_key_with_function_call": h_add_fc_key,
    "promise_batch_action_delete_key": h_delete_key, "promise_batch_action_delete_account": h_delete_account,
    "promise_batch_action_transfer_to_gas_key": h_transfer_to_gas_key,
    "promise_batch_action_add_gas_key_with_full_access": h_add_gas_full_key,
    "promise_batch_action_add_gas_key_with_function_call": h_add_gas_fc_key,
    "promise_yield_create": lambda inst, *a: yield_create(inst, False, a),
    "promise_yield_create_with_id": lambda inst, *a: yield_create(inst, True, a),
    "promise_yield_resume": lambda inst, *a: yield_resume(inst, False, a),
    "promise_yield_resume_with_yield_id": lambda inst, *a: yield_resume(inst, True, a),
    "promise_results_count": h_results_count, "promise_result": h_promise_result,
    "storage_write": h_storage_write, "storage_read": h_storage_read, "storage_remove": h_storage_remove,
    "storage_has_key": h_storage_has_key,
    "storage_iter_prefix": _deprecated("storage_iter_prefix"), "storage_iter_range": _deprecated("storage_iter_range"),
    "storage_iter_next": _deprecated("storage_iter_next"),
    "validator_stake": h_validator_stake, "validator_total_stake": h_validator_total,
}
assert set(HANDLERS) | OOD_HOSTS == set(HOST), set(HOST) - set(HANDLERS) - OOD_HOSTS


# ----------------------------------------------------------------------------------------------
# Running a contract

def run_case(prepaid, wasm, tok, full=False, method="main", store=None, prepared=None):
    try:
        m = prepared if prepared is not None else prepare(wasm)
    except PrepError as e:
        return f"abort 0 0 CompilationError(PrepareError({e.args[0]}))" + (EMPTY_FULL if full else "")
    except OutOfDomain as e:
        return f"out-of-domain {e.args[0]}"
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    ctx = Ctx(tok)
    defined = [f for f in m.funcs if not f.imported]
    for f in defined:
        if len(f.params) + len(f.locals) > ENGINE_LOCALS:
            return (f"abort 0 0 CompilationError(WasmtimeCompileError {{ msg: \"failed to compile: "
                    f"wasm[0]::function[{f.idx + 3}]\" }})") + (EMPTY_FULL if full else "")
    if prepaid > MAX_GAS_BURNT:
        return "unmodeled prepaid above max_gas_burnt"
    gc = GasCounter(prepaid)
    inst = Instance()
    inst.gc = gc
    inst.ctx = ctx
    inst.prof = {}
    inst.act_gas = 0
    inst.send_compute = 0
    inst.regs = {}
    inst.reg_usage = 0
    inst.logs = []
    inst.total_log = 0
    inst.alog = []
    inst.rcpt_recv = {}
    inst.actions = {}
    inst.store = store if store is not None else nearstore.MockStore()
    inst.store.last_inst = inst
    inst.storage_usage = 1000
    inst.data_counter = 0
    inst.yields = set()
    inst.yields_by_id = {}
    inst.yield_data = {}
    inst.ret = None
    inst.promises = []
    inst.balance = ctx.balance + ctx.deposit

    def extra():
        if not full:
            return ""
        trie = sorted(f"{k.hex()}={v.hex()}" for k, v in inst.store.items())
        return (f" || compute {compute_usage(inst)} || logs {','.join(l.hex() for l in inst.logs)} || actions "
                f"{';'.join(inst.alog)} || trie {','.join(trie)}")

    def abort(err):
        return f"abort {gc.burnt} {gc.burnt + gc.promises} {err}" + extra()

    def nop(err):
        return f"abort 0 0 {err}" + (EMPTY_FULL if full else "")

    # loading fee
    # (profiled as the ext costs contract_loading_bytes / contract_loading_base: checkpoint 3b finding)
    try:
        b0 = gc.burnt
        try:
            gc.pay_per(LOAD_BYTES, len(wasm))
        finally:
            inst.prof["contract_loading_bytes"] = gc.burnt - b0
        b0 = gc.burnt
        try:
            gc.pay_base(LOAD_BASE)
        finally:
            inst.prof["contract_loading_base"] = gc.burnt - b0
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
    ex = m.exports.get(method)
    if ex is None or ex[0] != 0:
        return nop("MethodResolveError(MethodNotFound)")
    mainf = m.funcs[ex[1]]
    if (mainf.params, mainf.results) != ((), ()):
        return nop("MethodResolveError(MethodInvalidSignature)")
    try:
        for f in defined:
            compile_func(m, f)
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    inst.m = m
    inst.g = gc.remaining()
    inst.stack = STACK_BUDGET
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
    except OutOfDomain as e:
        return f"out-of-domain {e.args[0]}"
    except Unmodeled as e:
        return f"unmodeled {e.args[0]}"
    except RecursionError:
        return "unmodeled python recursion"
    except nearstore.StorageError as e:
        return f"unmodeled storage error {e.args[0]}"
    if inst.ret is None:
        ret = "-"
    elif isinstance(inst.ret, tuple):
        ret = f"receipt{inst.ret[1]}"
    else:
        ret = inst.ret.hex()
    return f"ok {gc.burnt} {gc.burnt + gc.promises} {ret} {inst.balance}" + extra()


EMPTY_FULL = " || compute 0 || logs  || actions  || trie "


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


CHUNK_SLOTS = ["storage_write_base", "storage_read_base", "storage_read_key_byte", "storage_read_value_byte",
               "storage_large_read_overhead_base", "storage_large_read_overhead_byte", "storage_remove_base",
               "storage_has_key_base", "storage_has_key_byte", "touching_trie_node", "read_cached_trie_node"]


CHUNK_DELTAS = False   # --deltas: append ` d=<recorded growth of the receipt>` (section 4.5) to each call line


def chunk_lines(wasm, line):
    """Replay one `C <prev_root> <n> <node>... <k> (<account> <prepaid> <args|-> <14 expected>)...` line
    (d3-trie-accounting.md section 5) with the trie-backed store; -> one output line per call."""
    global CURRENT_ACCOUNT
    t = line.split(" ")
    if t[0] != "C":
        raise ValueError("not a chunk line")
    root = bytes.fromhex(t[1])
    n = int(t[2])
    chunk = nearstore.Chunk(root, [bytes.fromhex(x) for x in t[3:3 + n]])
    k = int(t[3 + n])
    out = []
    for j in range(k):
        b = 4 + n + 17 * j
        account, prepaid, args = t[b], int(t[b + 1]), t[b + 2]
        CURRENT_ACCOUNT = account.encode()
        store = chunk.store_for(account.encode())
        tok = "input=" + ("" if args == "-" else args)
        res = run_case(prepaid, wasm, tok, method="run", store=store)
        inst = store.last_inst
        status = res.split(" ", 1)[0]
        if status not in ("ok", "abort"):
            out.append(res)
            continue
        store.finish(status == "ok")
        host = sum(inst.prof.values())
        wasm_gas = inst.gc.burnt - inst.act_gas - host
        slots = " ".join(str(inst.prof.get(s, 0)) for s in CHUNK_SLOTS)
        st = "ok" if status == "ok" else "fail:" + failure_kind(res.split(" ", 3)[3])
        out.append(f"{st} {wasm_gas} {host} {slots}" + (f" d={chunk.upper - store.before}" if CHUNK_DELTAS else ""))
    return out


def failure_kind(err):
    """`HostError(GasExceeded)` -> GasExceeded, `HostError(X { .. })` -> X, `WasmTrap(..)` -> WasmTrap,
    `LinkError { .. }` -> LinkError (section 5: the HostError variant name, otherwise the variant inside
    FunctionCallError)."""
    if err.startswith("HostError("):
        err = err[len("HostError("):]
    m = re.match(r"[A-Za-z0-9_]+", err)
    return m.group(0) if m else err


def main_chunk(code_file):
    wasm = bytes.fromhex(open(code_file).read().strip())
    out = sys.stdout
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        k = int(line.split(" ")[3 + int(line.split(" ")[2])])
        try:
            res = chunk_lines(wasm, line)
        except Exception as e:  # never crash the stream; keep one line per call
            res = [f"unmodeled internal error {type(e).__name__}: {e}"] * k
        out.write("".join(r + "\n" for r in res))
        out.flush()


def main():
    sys.setrecursionlimit(100000)
    argv = sys.argv[1:]
    if "--chunk" in argv:
        global CHUNK_DELTAS
        CHUNK_DELTAS = "--deltas" in argv
        return main_chunk(argv[argv.index("--chunk") + 1])
    cp = "--charge-points" in argv
    full = "--full" in argv
    global TRACE
    TRACE = "--trace" in argv
    out = sys.stdout
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        parts = line.split(" ")
        prepaid = int(parts[0])
        wasm = bytes.fromhex(parts[1])
        tok = parts[2] if len(parts) > 2 else None
        try:
            if cp:
                res = charge_points_line(wasm)
            else:
                res = run_case(prepaid, wasm, tok, full)
        except Exception as e:  # never crash the stream
            res = f"unmodeled internal error {type(e).__name__}: {e}"
        out.write(res + "\n")
        out.flush()


if __name__ == "__main__":
    main()
