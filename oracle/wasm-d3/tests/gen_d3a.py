#!/usr/bin/env python3
"""Random well-typed D3α contracts (integer WASM with reference types and bulk memory).

  gen_d3a.py N SEED  →  `<prepaid_gas> <hex>` per line

Each module: imports `env.value_return` (+ sometimes `env.panic`, `env.gas`); 1–4 functions with
random i32/i64 params/results; mutable/immutable i32/i64 globals; optionally a funcref table with
active/passive/declarative element segments; active and passive data segments (with a data count
section); an optional start function. Bodies are typed random code over i32/i64: every integer
operator, all load/store widths at random or edge addresses and offsets, memory.size/grow, bulk
memory, table and ref operators, call/call_indirect, block/loop/if with results, br/br_if/br_table
carrying values, return, unreachable, select. `main` ends by storing its locals and returning a
memory window, so the final state is observable. Prepaid gas ranges from below the loading fee up
to 300 Tgas; loops are counted or gas-bounded.
"""
import random
import sys
from wasmenc import *

MEM = 1024 * 65536
OPS32_BIN = list(range(0x6A, 0x79))
OPS64_BIN = list(range(0x7C, 0x8B))
REL32 = list(range(0x46, 0x50))
REL64 = list(range(0x51, 0x5B))
E32 = [0, 1, 2, 31, 32, 33, 0x7F, 0x80, 0xFF, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 0x10000]
E64 = [0, 1, 63, 64, 65, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
       0xFFFFFFFFFFFFFFFF]
LOAD32 = [(0x28, 2), (0x2C, 0), (0x2D, 0), (0x2E, 1), (0x2F, 1)]
LOAD64 = [(0x29, 3), (0x30, 0), (0x31, 0), (0x32, 1), (0x33, 1), (0x34, 2), (0x35, 2)]
STORE32 = [(0x36, 2), (0x3A, 0), (0x3B, 1)]
STORE64 = [(0x37, 3), (0x3C, 0), (0x3D, 1), (0x3E, 2)]


class Fn:
    def __init__(self, g, params, results, nloc32, nloc64):
        self.g, self.r = g, g.rng
        self.params, self.results = params, results
        self.locals = params + [I32] * nloc32 + [I64] * nloc64
        self.loc_decl = [(n, t) for n, t in [(nloc32, I32), (nloc64, I64)] if n]
        self.code = bytearray()
        self.labels = []     # innermost last: None (arity 0) or value type

    def e(self, *bs):
        for b in bs:
            self.code += bytes([b]) if isinstance(b, int) else b

    def locs(self, t):
        return [i for i, x in enumerate(self.locals) if x == t]

    def const(self, t):
        r = self.r
        if t == I32:
            v = r.choice(E32) if r.random() < 0.4 else (r.randrange(300) if r.random() < 0.6 else r.getrandbits(32))
            self.e(i32c(v))
        else:
            v = r.choice(E64) if r.random() < 0.4 else (r.randrange(300) if r.random() < 0.6 else r.getrandbits(64))
            self.e(i64c(v))

    def addr(self, d):
        r, x = self.r, self.r.random()
        if x < 0.6:
            self.e(i32c(r.randrange(0, 2048)))
        elif x < 0.75:
            self.e(i32c(MEM - r.randrange(0, 16)))
        elif x < 0.85:
            self.expr(I32, d)
            self.e(i32c(0xFFF), 0x71)
        else:
            self.expr(I32, d)

    def off(self):
        x = self.r.random()
        return self.r.randrange(64) if x < 0.8 else (self.r.randrange(1 << 16) if x < 0.95 else self.r.getrandbits(32))

    def count(self, d):
        x = self.r.random()
        if x < 0.7:
            self.e(i32c(self.r.randrange(0, 40)))
        elif x < 0.85:
            self.e(i32c(self.r.choice([MEM, MEM + 1, 0xFFFFFFFF, 1024, 2048])))
        else:
            self.expr(I32, d)

    def label_depths(self, t):
        n = len(self.labels)
        return [n - 1 - i for i, k in enumerate(self.labels) if k == t]

    def expr(self, t, d):
        r = self.r
        g = self.g
        if d <= 0 or r.random() < 0.15:
            ls = self.locs(t)
            if ls and r.random() < 0.5:
                self.e(0x20, uleb(r.choice(ls)))
            else:
                self.const(t)
            return
        c = r.random()
        if c < 0.25:
            self.expr(t, d - 1); self.expr(t, d - 1)
            self.e(r.choice(OPS32_BIN if t == I32 else OPS64_BIN))
        elif c < 0.32:
            if t == I32:
                tt = r.choice([I32, I64])
                self.expr(tt, d - 1); self.expr(tt, d - 1); self.e(r.choice(REL32 if tt == I32 else REL64))
            else:
                self.expr(I64, d - 1); self.e(r.choice([0x79, 0x7A, 0x7B, 0xC2, 0xC3, 0xC4]))
        elif c < 0.38:
            if t == I32:
                x = r.random()
                if x < 0.3:
                    self.expr(I64, d - 1); self.e(0xA7)
                elif x < 0.5:
                    self.expr(I64, d - 1); self.e(0x50)
                else:
                    self.expr(I32, d - 1); self.e(r.choice([0x45, 0x67, 0x68, 0x69, 0xC0, 0xC1]))
            else:
                self.expr(I32, d - 1); self.e(r.choice([0xAC, 0xAD]))
        elif c < 0.46:
            self.addr(d - 1)
            op, al = r.choice(LOAD32 if t == I32 else LOAD64)
            self.e(op, uleb(r.randrange(al + 1)), uleb(self.off()))
        elif c < 0.49:
            if t == I32:
                self.e(0x3F, 0x00) if r.random() < 0.5 else (self.count(d - 1), self.e(0x40, 0x00))
            else:
                self.const(t)
        elif c < 0.53:
            self.expr(t, d - 1); self.expr(t, d - 1); self.expr(I32, d - 1)
            self.e(0x1B) if r.random() < 0.5 else self.e(0x1C, 0x01, t)
        elif c < 0.57:
            ls = self.locs(t)
            if ls:
                self.expr(t, d - 1); self.e(0x22, uleb(r.choice(ls)))
            else:
                self.const(t)
        elif c < 0.61:
            gs = [i for i, (gt, _) in enumerate(g.globals) if gt == t]
            self.e(0x23, uleb(r.choice(gs))) if gs else self.const(t)
        elif c < 0.68:
            self.e(0x02, t)
            self.labels.append(t)
            self.stmts(d - 1, r.randrange(0, 3))
            if r.random() < 0.3:
                ds = self.label_depths(t)
                self.expr(t, d - 1)
                if r.random() < 0.5:
                    self.expr(I32, d - 1); self.e(0x0D, uleb(r.choice(ds)))
                else:
                    self.e(0x0C, uleb(r.choice(ds)))
                    self.labels.pop(); self.e(0x0B)
                    return
            else:
                self.expr(t, d - 1)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.74:
            self.expr(I32, d - 1)
            self.e(0x04, t)
            self.labels.append(t)
            self.stmts(d - 1, r.randrange(0, 2)); self.expr(t, d - 1)
            self.e(0x05)
            self.stmts(d - 1, r.randrange(0, 2)); self.expr(t, d - 1)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.80:
            cands = [f for f in g.fsigs if len(f[2]) == 1 and f[2][0] == t]
            if cands and g.depth_ok():
                fi, ps, _ = r.choice(cands)
                for p in ps:
                    self.expr(p, d - 1)
                if g.table and r.random() < 0.4:
                    self.e(i32c(r.randrange(0, g.table + 2)))
                    self.e(0x11, uleb(g.m.type(ps, [t])), 0x00)
                else:
                    self.e(0x10, uleb(fi))
            else:
                self.const(t)
        elif c < 0.84 and t == I32 and g.table:
            x = r.random()
            if x < 0.3:
                self.e(0xFC, 0x10, 0x00)
            elif x < 0.6:
                self.e(0xD0, 0x70) if r.random() < 0.5 else self.e(0xD2, uleb(r.choice(g.declared)))
                self.count(d - 1); self.e(0xFC, 0x0F, 0x00)
            else:
                self.e(i32c(r.randrange(0, g.table + 2)), 0x25, 0x00, 0xD1)
        else:
            self.expr(t, d - 1); self.expr(t, d - 1)
            self.e(r.choice(OPS32_BIN if t == I32 else OPS64_BIN))

    def stmt(self, d):
        r, g = self.r, self.g
        c = r.random()
        if c < 0.18 or d <= 0:
            t = r.choice([I32, I64])
            ls = self.locs(t)
            if ls:
                self.expr(t, max(d, 1)); self.e(0x21, uleb(r.choice(ls)))
            else:
                self.expr(t, max(d, 1)); self.e(0x1A)
        elif c < 0.30:
            t = r.choice([I32, I64])
            self.addr(d - 1); self.expr(t, d - 1)
            op, al = r.choice(STORE32 if t == I32 else STORE64)
            self.e(op, uleb(r.randrange(al + 1)), uleb(self.off()))
        elif c < 0.34:
            gs = [i for i, (gt, mu) in enumerate(g.globals) if mu]
            if gs:
                gi = r.choice(gs)
                self.expr(g.globals[gi][0], d - 1); self.e(0x24, uleb(gi))
        elif c < 0.42:
            self.e(0x02, 0x40); self.labels.append(None)
            self.stmts(d - 1, r.randrange(0, 4))
            self.terminator(0.4)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.48:
            ls = self.locs(I32)
            if ls:
                cl = r.choice(ls)
                self.e(i32c(r.randrange(0, 5)), 0x21, uleb(cl))
                self.e(0x03, 0x40); self.labels.append(None)
                self.stmts(d - 1, r.randrange(0, 3))
                self.e(0x20, uleb(cl), i32c(1), 0x6B, 0x22, uleb(cl), 0x0D, 0x00)
                self.labels.pop(); self.e(0x0B)
        elif c < 0.50 and g.unbounded:
            self.e(0x03, 0x40); self.labels.append(None)
            self.stmts(d - 1, r.randrange(0, 3))
            self.expr(I32, d - 1); self.e(0x0D, 0x00)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.58:
            self.expr(I32, d - 1)
            self.e(0x04, 0x40); self.labels.append(None)
            self.stmts(d - 1, r.randrange(0, 3))
            if r.random() < 0.6:
                self.e(0x05); self.stmts(d - 1, r.randrange(0, 3))
            self.labels.pop(); self.e(0x0B)
        elif c < 0.63:
            ds = self.label_depths(None)
            if ds:
                self.expr(I32, d - 1); self.e(0x0D, uleb(r.choice(ds)))
        elif c < 0.70:
            x = r.random()
            if x < 0.35:
                self.count(d - 1); self.count(d - 1); self.count(d - 1); self.e(0xFC, 0x0A, 0x00, 0x00)
            elif x < 0.7:
                self.addr(d - 1); self.expr(I32, d - 1); self.count(d - 1); self.e(0xFC, 0x0B, 0x00)
            elif g.ndata:
                seg = r.randrange(g.ndata)
                if r.random() < 0.2:
                    self.e(0xFC, 0x09, uleb(seg))
                else:
                    self.addr(d - 1); self.count(d - 1); self.count(d - 1); self.e(0xFC, 0x08, uleb(seg), 0x00)
        elif c < 0.75 and g.table:
            x = r.random()
            if x < 0.25:
                self.count(d - 1); self.e(0xD2, uleb(r.choice(g.declared))) if r.random() < 0.7 else self.e(0xD0, 0x70)
                self.e(0x26, 0x00)
            elif x < 0.5:
                self.count(d - 1); self.e(0xD2, uleb(r.choice(g.declared))); self.count(d - 1); self.e(0xFC, 0x11, 0x00)
            elif x < 0.7:
                self.count(d - 1); self.count(d - 1); self.count(d - 1); self.e(0xFC, 0x0E, 0x00, 0x00)
            elif x < 0.9:
                seg = r.randrange(g.nelem)
                self.count(d - 1); self.count(d - 1); self.count(d - 1); self.e(0xFC, 0x0C, uleb(seg), 0x00)
            else:
                self.e(0xFC, 0x0D, uleb(r.randrange(g.nelem)))
        elif c < 0.80:
            self.count(d - 1); self.e(0x40, 0x00, 0x1A)
        elif c < 0.85:
            self.e(i64c(r.randrange(0, 64) if r.random() < 0.9 else r.choice([-1, 1 << 40, 5_000_000])))
            self.e(i64c(r.randrange(0, 2048) if r.random() < 0.9 else MEM))
            self.e(0x10, uleb(g.m.vr))
        elif c < 0.86 and g.panic is not None:
            self.e(0x10, uleb(g.panic))
        elif c < 0.87 and g.gas is not None:
            self.count(d - 1); self.e(0x10, uleb(g.gas))
        elif c < 0.93:
            cands = [f for f in g.fsigs if not f[2]]
            if cands and g.depth_ok():
                fi, ps, _ = r.choice(cands)
                for p in ps:
                    self.expr(p, d - 1)
                if g.table and r.random() < 0.4:
                    self.e(i32c(r.randrange(0, g.table + 2)), 0x11, uleb(g.m.type(ps, [])), 0x00)
                else:
                    self.e(0x10, uleb(fi))
            else:
                ts = [f for f in g.fsigs if f[2]]
                if ts and g.depth_ok():
                    fi, ps, rs = r.choice(ts)
                    for p in ps:
                        self.expr(p, d - 1)
                    self.e(0x10, uleb(fi), 0x1A)
        else:
            self.e(0x01)

    def stmts(self, d, n):
        for _ in range(n):
            self.stmt(d)

    def terminator(self, p):
        r = self.r
        if r.random() >= p:
            return
        c = r.random()
        ds = self.label_depths(None)
        if c < 0.4 and ds:
            self.e(0x0C, uleb(r.choice(ds)))
        elif c < 0.65 and ds:
            self.expr(I32, 1)
            tg = [r.choice(ds) for _ in range(r.randrange(0, 4))]
            self.e(0x0E, vec([uleb(x) for x in tg]), uleb(r.choice(ds)))
        elif c < 0.85 and not self.results:
            self.e(0x0F)
        elif c < 0.95 and self.results:
            self.expr(self.results[0], 1); self.e(0x0F)
        else:
            self.e(0x00)

    def body(self, nst, depth, is_main):
        self.labels.append(self.results[0] if self.results else None)
        self.stmts(depth, nst)
        if is_main:
            for i, t in enumerate(self.locals):
                self.e(i32c(4096 + 8 * i), 0x20, uleb(i), 0x37 if t == I64 else 0x36, 0x03 if t == I64 else 0x02, 0x00)
            self.e(i64c(8 * len(self.locals) + 64), i64c(4096 - 64), 0x10, uleb(self.g.m.vr))
        else:
            if self.results:
                self.expr(self.results[0], 2)
            else:
                self.terminator(0.2)
        self.labels.pop()
        return bytes(self.code)


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.calls = 0

    def depth_ok(self):
        self.calls += 1
        return self.calls < 40

    def case(self):
        r = self.rng
        m = base_module(memory=True)
        self.m = m
        self.panic = m.import_func("env", "panic", [], []) if r.random() < 0.3 else None
        self.gas = m.import_func("env", "gas", [I32], []) if r.random() < 0.15 else None
        self.unbounded = r.random() < 0.15
        self.calls = 0
        self.globals = []
        for _ in range(r.randrange(0, 4)):
            t = r.choice([I32, I64])
            mu = r.random() < 0.7
            self.globals.append((t, mu))
            m.globals.append((t, mu, (i32c(r.getrandbits(32)) if t == I32 else i64c(r.getrandbits(64))) + b"\x0b"))
        nimp = len(m.imports)
        nf = r.randrange(1, 5)
        sigs = []
        for k in range(nf):
            if k == 0:
                sigs.append(([], []))
            else:
                ps = [r.choice([I32, I64]) for _ in range(r.randrange(0, 4))]
                rs = [r.choice([I32, I64])] if r.random() < 0.6 else []
                sigs.append((ps, rs))
        self.fsigs = [(nimp + k, ps, rs) for k, (ps, rs) in enumerate(sigs)]
        self.table = 0
        self.declared = [nimp]
        self.nelem = 0
        if r.random() < 0.5:
            self.table = r.randrange(1, 8)
            m.tables.append((FUNCREF, self.table, r.choice([None, self.table, self.table + 3, 10000])))
            fis = [uleb(nimp + r.randrange(nf)) for _ in range(r.randrange(1, self.table + 1))]
            off = r.randrange(0, self.table) if r.random() < 0.9 else self.table
            m.elems.append(b"\x00" + i32c(off) + b"\x0b" + vec(fis))
            m.elems.append(b"\x01\x00" + vec([uleb(nimp + r.randrange(nf)) for _ in range(r.randrange(0, 4))]))
            m.elems.append(b"\x03\x00" + vec([uleb(nimp + k) for k in range(nf)]))
            self.declared = [nimp + k for k in range(nf)]
            self.nelem = 3
        self.ndata = 0
        if r.random() < 0.6:
            m.datacount = True
            for _ in range(r.randrange(1, 3)):
                payload = bytes(r.getrandbits(8) for _ in range(r.randrange(0, 24)))
                if r.random() < 0.5:
                    off = r.randrange(0, 4096) if r.random() < 0.9 else MEM - r.randrange(0, 24)
                    m.datas.append(b"\x00" + i32c(off) + b"\x0b" + vec([bytes([x]) for x in payload]))
                else:
                    m.datas.append(b"\x01" + vec([bytes([x]) for x in payload]))
            self.ndata = len(m.datas)
        bodies = []
        for k, (ps, rs) in enumerate(sigs):
            f = Fn(self, ps, rs, r.randrange(1 if k == 0 else 0, 5), r.randrange(0, 3))
            b = f.body(r.randrange(1, 7), r.randrange(1, 4), k == 0)
            m.func(ps, rs, f.loc_decl, b)
        m.exports.append(("main", 0, nimp))
        if nf > 1 and r.random() < 0.15 and not sigs[1][0] and not sigs[1][1]:
            m.start = nimp + 1
        x = r.random()
        if x < 0.08:
            gas = r.randrange(0, 400_000_000)
        elif x < 0.5:
            gas = int(10 ** r.uniform(8.5, 11.5))
        elif self.unbounded or nf > 1:
            gas = int(10 ** r.uniform(10.5, 12.3))
        else:
            gas = 300 * 10**12
        return gas, m.encode()


def main():
    n = int(sys.argv[1])
    seed = int(sys.argv[2])
    g = Gen(random.Random(seed))
    for _ in range(n):
        gas, w = g.case()
        print(gas, w.hex())


if __name__ == "__main__":
    main()
