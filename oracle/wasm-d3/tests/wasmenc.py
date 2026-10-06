"""Minimal WebAssembly binary encoder for the D3 difftests (no third-party deps)."""

I32, I64, F32, F64, FUNCREF, EXTERNREF = 0x7F, 0x7E, 0x7D, 0x7C, 0x70, 0x6F
EMPTY = 0x40


def uleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def sleb(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if (n == 0 and not (b & 0x40)) or (n == -1 and (b & 0x40)):
            out.append(b)
            return bytes(out)
        out.append(b | 0x80)


def s32(v):
    v &= 0xFFFFFFFF
    return v - (1 << 32) if v & 0x80000000 else v


def s64(v):
    v &= 0xFFFFFFFFFFFFFFFF
    return v - (1 << 64) if v & (1 << 63) else v


def vec(items):
    return uleb(len(items)) + b"".join(items)


def name(s):
    b = s.encode()
    return uleb(len(b)) + b


def section(sid, payload):
    return bytes([sid]) + uleb(len(payload)) + payload


def i32c(v):
    return b"\x41" + sleb(s32(v))


def i64c(v):
    return b"\x42" + sleb(s64(v))


def functype(params, results):
    return b"\x60" + vec([bytes([p]) for p in params]) + vec([bytes([r]) for r in results])


class Module:
    """Sections are added in canonical order by `encode`."""

    def __init__(self):
        self.types = []          # bytes of functype
        self.imports = []        # (module, name, typeidx)
        self.funcs = []          # (typeidx, locals [(n, t)], body bytes without final end)
        self.tables = []         # (elemtype, min, max|None)
        self.memory = None       # (min, max|None)
        self.globals = []        # (type, mutable, init bytes incl end)
        self.exports = []        # (name, kind, idx)
        self.start = None
        self.elems = []          # raw element segment bytes
        self.datas = []          # raw data segment bytes
        self.datacount = False

    def type(self, params, results):
        t = functype(params, results)
        if t not in self.types:
            self.types.append(t)
        return self.types.index(t)

    def import_func(self, mod, nm, params, results):
        self.imports.append((mod, nm, self.type(params, results)))
        return len(self.imports) - 1

    def func(self, params, results, locals_, body):
        self.funcs.append((self.type(params, results), locals_, body))
        return len(self.imports) + len(self.funcs) - 1

    def encode(self):
        out = b"\x00asm\x01\x00\x00\x00"
        if self.types:
            out += section(1, vec(self.types))
        if self.imports:
            out += section(2, vec([name(m) + name(n) + (b"\x02\x00\x01" if t is None else b"\x00" + uleb(t))
                                   for m, n, t in self.imports]))
        if self.funcs:
            out += section(3, vec([uleb(t) for t, _, _ in self.funcs]))
        if self.tables:
            out += section(4, vec([bytes([et]) + (b"\x00" + uleb(mn) if mx is None else b"\x01" + uleb(mn) + uleb(mx))
                                   for et, mn, mx in self.tables]))
        if self.memory is not None:
            mn, mx = self.memory
            out += section(5, vec([b"\x00" + uleb(mn) if mx is None else b"\x01" + uleb(mn) + uleb(mx)]))
        if self.globals:
            out += section(6, vec([bytes([t, 1 if m else 0]) + init for t, m, init in self.globals]))
        if self.exports:
            out += section(7, vec([name(n) + bytes([k]) + uleb(i) for n, k, i in self.exports]))
        if self.start is not None:
            out += section(8, uleb(self.start))
        if self.elems:
            out += section(9, vec(self.elems))
        if self.datacount:
            out += section(12, uleb(len(self.datas)))
        if self.funcs:
            bodies = []
            for _, locals_, body in self.funcs:
                b = vec([uleb(n) + bytes([t]) for n, t in locals_]) + body + b"\x0b"
                bodies.append(uleb(len(b)) + b)
            out += section(10, vec(bodies))
        if self.datas:
            out += section(11, vec(self.datas))
        return out


def value_return_tail(mod, nbytes, ptr=0):
    """Instructions returning memory[ptr, ptr+nbytes) via env.value_return (import must exist)."""
    return i64c(nbytes) + i64c(ptr) + b"\x10" + uleb(mod.vr)


def base_module(memory=True):
    m = Module()
    m.vr = m.import_func("env", "value_return", [I64, I64], [])
    if memory:
        m.memory = (1, None)
    return m
