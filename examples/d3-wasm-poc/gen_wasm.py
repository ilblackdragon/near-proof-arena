#!/usr/bin/env python3
"""Random NEAR-contract generator for the D3 WASM PoC differential test.

Emits one case per line: `<prepaid_gas> <wasm_hex>`. Every module is a valid
WebAssembly 1.0 module in the PoC subset (see README.md):

  imports  env.value_return (i64,i64)->(), env.panic ()->()
  funcs    main ()->() exported as "main", plus 0..2 helpers ()->()
  values   i32 (i64 only as host-call arguments: i64.const, i64.extend_i32_u)
  instrs   i32.const local.{get,set,tee} drop nop select, all i32 unop/binop/
           relop/testop, i32.{load,load8_u,store,store8} (any offset),
           memory.{size,grow}, block/loop/if/else/end (empty or i32 result),
           br br_if br_table return unreachable call

Families (chosen per case) target the semantic corners the PoC must get
exactly right: traps, out-of-gas at every granularity, finite-wasm's
per-basic-block charging window (GasLimitExceeded vs GasExceeded), stack
exhaustion through recursion, host-function error paths.
"""
import random
import sys

I32_EDGE = [0, 1, 2, 3, 4, 7, 8, 31, 32, 33, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE, 0x10000, 0xFFFF]
MEM_BYTES = 1024 * 65536  # initial_memory_pages = 1024 at PV86

UNOPS = [0x67, 0x68, 0x69]                     # clz ctz popcnt
BINOPS = list(range(0x6A, 0x79))                # add..rotr (incl. div/rem)
RELOPS = list(range(0x46, 0x50))                # eq..ge_u
MAX_GAS_BURNT = 10**15
OP = 822756


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


def vec(items):
    return uleb(len(items)) + b"".join(items)


def section(sid, payload):
    return bytes([sid]) + uleb(len(payload)) + payload


class Func:
    def __init__(self, gen, nlocals, is_main):
        self.g = gen
        self.nlocals = nlocals
        self.is_main = is_main
        self.code = bytearray()
        self.labels = []  # innermost last: 'v' (arity 0) or 'i' (arity 1 i32); loops are 'v'

    # ---- helpers
    def e(self, *bs):
        for b in bs:
            if isinstance(b, int):
                self.code.append(b)
            else:
                self.code.extend(b)

    def const(self, v):
        self.e(0x41, sleb(s32(v)))

    def rand_i32(self):
        r = self.g.rng
        x = r.random()
        if x < 0.35:
            return r.choice(I32_EDGE)
        if x < 0.75:
            return r.randrange(0, 300)
        return r.getrandbits(32)

    def local(self):
        return self.g.rng.randrange(self.nlocals)

    def label_depths(self, kind):
        n = len(self.labels)
        return [n - 1 - i for i, k in enumerate(self.labels) if k == kind]

    # ---- expressions: push exactly one i32
    def expr(self, d):
        r = self.g.rng
        if d <= 0:
            if r.random() < 0.5:
                self.const(self.rand_i32())
            else:
                self.e(0x20, uleb(self.local()))
            return
        c = r.random()
        if c < 0.12:
            self.const(self.rand_i32())
        elif c < 0.24:
            self.e(0x20, uleb(self.local()))
        elif c < 0.42:
            self.expr(d - 1); self.expr(d - 1); self.e(r.choice(BINOPS))
        elif c < 0.50:
            self.expr(d - 1); self.expr(d - 1); self.e(r.choice(RELOPS))
        elif c < 0.55:
            self.expr(d - 1); self.e(r.choice(UNOPS + [0x45]))
        elif c < 0.63:
            self.addr(d - 1)
            if r.random() < 0.6:
                self.e(0x28, uleb(2), uleb(self.offset()))
            else:
                self.e(0x2D, uleb(0), uleb(self.offset()))
        elif c < 0.66:
            self.e(0x3F, 0x00)
        elif c < 0.68:
            self.pages(d - 1); self.e(0x40, 0x00)
        elif c < 0.72:
            self.expr(d - 1); self.expr(d - 1); self.expr(d - 1); self.e(0x1B)
        elif c < 0.76:
            self.expr(d - 1); self.e(0x22, uleb(self.local()))
        elif c < 0.84:
            # block (result i32), optionally exiting with `br 0` carrying the value
            self.e(0x02, 0x7F)
            self.labels.append('i')
            self.stmts(d - 1, r.randrange(0, 3))
            if r.random() < 0.3:
                ds = self.label_depths('i')
                self.expr(d - 1)
                if r.random() < 0.5:
                    self.expr(d - 1); self.e(0x0D, uleb(r.choice(ds)))  # br_if keeps the value
                else:
                    self.e(0x0C, uleb(r.choice(ds)))                   # br: block ends here
                    self.labels.pop(); self.e(0x0B)
                    return
            else:
                self.expr(d - 1)
            self.labels.pop()
            self.e(0x0B)
        elif c < 0.92:
            self.expr(d - 1)
            self.e(0x04, 0x7F)
            self.labels.append('i')
            self.stmts(d - 1, r.randrange(0, 2)); self.expr(d - 1)
            self.e(0x05)
            self.stmts(d - 1, r.randrange(0, 2)); self.expr(d - 1)
            self.labels.pop()
            self.e(0x0B)
        else:
            self.expr(d - 1); self.expr(d - 1); self.e(r.choice(BINOPS))

    def offset(self):
        r = self.g.rng
        x = r.random()
        if x < 0.7:
            return r.randrange(0, 64)
        if x < 0.9:
            return r.randrange(0, 1 << 16)
        return r.getrandbits(32)

    def addr(self, d):
        r = self.g.rng
        x = r.random()
        if x < 0.6:
            self.const(r.randrange(0, 1200))
        elif x < 0.75:
            self.const(MEM_BYTES - r.randrange(0, 16))
        elif x < 0.85:
            self.expr(d); self.const(0xFFF); self.e(0x71)
        else:
            self.expr(d)

    def pages(self, d):
        r = self.g.rng
        x = r.random()
        if x < 0.6:
            self.const(r.randrange(0, 4))
        elif x < 0.8:
            self.const(r.choice([1024, 1025, 2048, 0xFFFFFFFF, 0x7FFFFFFF]))
        else:
            self.expr(d)

    def i64arg(self, small_max):
        r = self.g.rng
        x = r.random()
        if x < 0.85:
            self.const(r.randrange(0, small_max)); self.e(0xAD)    # i64.extend_i32_u
        elif x < 0.9:
            self.e(0x42, sleb(-1))                                 # u64::MAX: register path
        else:
            self.e(0x42, sleb(r.choice([1 << 40, 1 << 62, 5_000_000, MEM_BYTES - 3, MEM_BYTES + 1])))

    # ---- statements: stack-neutral
    def stmt(self, d):
        r = self.g.rng
        c = r.random()
        if c < 0.22 or d <= 0:
            self.expr(max(d, 1)); self.e(0x21, uleb(self.local()))
        elif c < 0.36:
            self.addr(d - 1); self.expr(d - 1)
            if r.random() < 0.6:
                self.e(0x36, uleb(2), uleb(self.offset()))
            else:
                self.e(0x3A, uleb(0), uleb(self.offset()))
        elif c < 0.40:
            self.expr(d - 1); self.e(0x1A)
        elif c < 0.42:
            self.e(0x01)
        elif c < 0.50:
            self.e(0x02, 0x40); self.labels.append('v')
            self.stmts(d - 1, r.randrange(0, 4))
            self.terminator_maybe(0.4)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.58:
            # counted loop
            cl = self.local()
            self.const(r.randrange(0, 6)); self.e(0x21, uleb(cl))
            self.e(0x03, 0x40); self.labels.append('v')
            self.stmts(d - 1, r.randrange(0, 3))
            self.e(0x20, uleb(cl)); self.const(1); self.e(0x6B, 0x22, uleb(cl))
            self.e(0x0D, 0x00)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.61 and self.g.allow_unbounded:
            self.e(0x03, 0x40); self.labels.append('v')
            self.stmts(d - 1, r.randrange(0, 3))
            self.expr(d - 1); self.e(0x0D, 0x00)
            self.labels.pop(); self.e(0x0B)
        elif c < 0.70:
            self.expr(d - 1)
            self.e(0x04, 0x40); self.labels.append('v')
            self.stmts(d - 1, r.randrange(0, 3))
            if r.random() < 0.6:
                self.e(0x05); self.stmts(d - 1, r.randrange(0, 3))
            self.labels.pop(); self.e(0x0B)
        elif c < 0.76:
            ds = self.label_depths('v')
            if ds:
                self.expr(d - 1); self.e(0x0D, uleb(r.choice(ds)))
            else:
                self.e(0x01)
        elif c < 0.81:
            self.pages(d - 1); self.e(0x40, 0x00)
            if r.random() < 0.5:
                self.e(0x1A)
            else:
                self.e(0x21, uleb(self.local()))
        elif c < 0.86:
            self.i64arg(1100); self.i64arg(1200 if r.random() < 0.9 else MEM_BYTES); self.e(0x10, 0x00)
        elif c < 0.87:
            self.e(0x10, 0x01)  # panic
        elif c < 0.92 and self.g.nhelpers:
            self.e(0x10, uleb(3 + r.randrange(self.g.nhelpers)))
        else:
            self.e(0x01)

    def stmts(self, d, n):
        for _ in range(n):
            self.stmt(d)

    def terminator_maybe(self, p):
        """Optionally end the current (arity-0) block with an instruction making the stack polymorphic."""
        r = self.g.rng
        if r.random() >= p:
            return
        c = r.random()
        ds = self.label_depths('v')
        if c < 0.45 and ds:
            self.e(0x0C, uleb(r.choice(ds)))
        elif c < 0.7 and ds:
            self.expr(1)
            tgts = [r.choice(ds) for _ in range(r.randrange(0, 4))]
            self.e(0x0E, vec([uleb(t) for t in tgts]), uleb(r.choice(ds)))
        elif c < 0.85:
            self.e(0x0F)
        else:
            self.e(0x00)

    def body(self, nstmts, depth):
        self.labels.append('v')  # the function-level label
        self.stmts(depth, nstmts)
        if self.is_main:
            # make the final state observable: locals -> memory[1024..], return memory[0..1024+4n)
            for i in range(self.nlocals):
                self.const(1024 + 4 * i); self.e(0x20, uleb(i)); self.e(0x36, uleb(2), uleb(0))
            self.const(1024 + 4 * self.nlocals); self.e(0xAD); self.const(0); self.e(0xAD)
            self.e(0x10, 0x00)
        else:
            self.terminator_maybe(0.2)
        self.labels.pop()
        self.e(0x0B)
        locals_ = vec([uleb(self.nlocals) + bytes([0x7F])]) if self.nlocals else vec([])
        b = locals_ + bytes(self.code)
        return uleb(len(b)) + b


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.allow_unbounded = False
        self.nhelpers = 0

    def module(self, funcs_bodies, declare_memory):
        types = vec([b"\x60\x00\x00", b"\x60\x02\x7e\x7e\x00"])
        imports = vec([
            vec([b"e", b"n", b"v"])[0:0] + uleb(3) + b"env" + uleb(12) + b"value_return" + b"\x00" + uleb(1),
            uleb(3) + b"env" + uleb(5) + b"panic" + b"\x00" + uleb(0),
        ])
        funcs = vec([uleb(0) for _ in funcs_bodies])
        out = b"\x00asm\x01\x00\x00\x00"
        out += section(1, types) + section(2, imports) + section(3, funcs)
        if declare_memory:
            out += section(5, vec([b"\x00" + uleb(declare_memory)]))
        out += section(7, vec([uleb(4) + b"main" + b"\x00" + uleb(2)]))
        out += section(10, vec(funcs_bodies))
        return out

    def random_case(self):
        r = self.rng
        self.nhelpers = r.choice([0, 0, 1, 2])
        self.allow_unbounded = r.random() < 0.15
        bodies = []
        main = Func(self, r.randrange(1, 7), True)
        bodies.append(main.body(r.randrange(1, 9), r.randrange(1, 4)))
        for _ in range(self.nhelpers):
            h = Func(self, r.randrange(1, 5), False)
            bodies.append(h.body(r.randrange(0, 5), r.randrange(1, 3)))
        wasm = self.module(bodies, r.choice([1] * 12 + [17, 3000, 0]))
        x = r.random()
        if x < 0.1:
            gas = r.randrange(0, 400_000_000)               # around the contract-loading fee
        elif x < 0.5:
            gas = int(10 ** r.uniform(8.5, 11.5))
        elif self.allow_unbounded or self.nhelpers:
            gas = int(10 ** r.uniform(11, 12.3))
        else:
            gas = 300 * 10**12
        return gas, wasm

    def window_case(self, k):
        """finite-wasm charges a whole basic block up front: with prepaid just below
        max_gas_burnt, out-of-gas inside a long pure run reports GasLimitExceeded
        (block-level) where an instruction-level meter would report GasExceeded.
        `memory.grow(n)` (fee 26,328,192 + 822,756 n, paid even when growth fails)
        burns ~1e15 cheaply; n is solved so that the gas left after it is k ops."""
        r = self.rng
        n_pure = r.randrange(20, 60)
        consts = [r.randrange(0, 100) for _ in range(n_pure)]
        delta = r.randrange(0, 40) * OP + r.randrange(0, OP)
        prepaid = MAX_GAS_BURNT - delta

        def build(n_pages):
            f = Func(self, 2, True)
            f.labels.append('v')
            f.const(n_pages); f.e(0x40, 0x00, 0x1A)
            for c in consts:                                   # one long pure range
                f.const(c); f.e(0x21, 0x00)
            f.labels.pop()
            b = vec([uleb(2) + b"\x7f"]) + bytes(f.code) + b"\x0b"
            return self.module([uleb(len(b)) + b], 1)

        probe = build(1215422000)
        loading = 35445963 + 1089295 * len(probe)
        prologue = (64 + 8 + 7) // 8 * OP
        before = loading + prologue + OP + 26328192         # + the i32.const point
        n_pages = (prepaid - before) // OP - k
        wasm = build(n_pages)
        assert len(wasm) == len(probe)
        return prepaid, wasm

    def recursion_case(self):
        r = self.rng
        self.nhelpers = 1
        f = Func(self, r.randrange(1, 4), True)
        h = Func(self, r.randrange(1, 40), False)
        f.labels.append('v'); f.e(0x10, 0x03)
        for i in range(f.nlocals):
            f.const(1024 + 4 * i); f.e(0x20, uleb(i)); f.e(0x36, uleb(2), uleb(0))
        f.labels.pop(); f.e(0x0B)
        fb = vec([uleb(f.nlocals) + b"\x7f"]) + bytes(f.code)
        h.labels.append('v')
        for _ in range(r.randrange(0, 4)):
            h.expr(2); h.e(0x1A)
        h.e(0x10, 0x03)
        h.labels.pop(); h.e(0x0B)
        hb = (vec([uleb(h.nlocals) + b"\x7f"]) if h.nlocals else vec([])) + bytes(h.code)
        wasm = self.module([uleb(len(fb)) + fb, uleb(len(hb)) + hb], 1)
        gas = r.choice([300 * 10**12, int(10 ** r.uniform(9, 11))])
        return gas, wasm


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 1000
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    g = Gen(random.Random(seed))
    for i in range(n):
        x = g.rng.random()
        if x < 0.06:
            gas, wasm = g.window_case(g.rng.randrange(-10, 130))
        elif x < 0.10:
            gas, wasm = g.recursion_case()
        else:
            gas, wasm = g.random_case()
        print(gas, wasm.hex())


if __name__ == "__main__":
    main()
