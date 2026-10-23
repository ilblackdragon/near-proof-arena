#!/usr/bin/env python3
"""Reference IEEE 754 binary32/binary64 semantics for the L2 float differential test.

This is a *test oracle in Python*, not part of the specification: it uses the host's IEEE
arithmetic (`struct` round-trips through C `float`/`double`, which are IEEE binary32/binary64 on
every supported platform) and then applies the two rules that nearcore's Wasmtime configuration
fixes beyond IEEE (`cranelift_nan_canonicalization(true)`, Winch on x86_64):

  * every operation that can produce a NaN yields the *canonical* NaN, and
  * `abs`, `neg`, `copysign`, `reinterpret` are bit operations that preserve NaN payloads.

`difftest_float.py` compares this reference with `NearSpecV3.Wasm.evalFloatOp` and, for a sample,
with pinned nearcore's own engine (`oracle/wasm-d3` harness), so the Lean semantics are anchored to
both a readable statement of IEEE and the pinned target.

Usage as a filter: stdin `<op> <a-hex> <b-hex>` → stdout one line (`<hex>` or `trap`).
"""
import math
import struct
import sys

CAN32 = 0x7FC00000
CAN64 = 0x7FF8000000000000


def f32(bits):
    return struct.unpack(">f", struct.pack(">I", bits & 0xFFFFFFFF))[0]


def f64(bits):
    return struct.unpack(">d", struct.pack(">Q", bits & 0xFFFFFFFFFFFFFFFF))[0]


def b32(x):
    if isinstance(x, float):
        try:
            return struct.unpack(">I", struct.pack(">f", x))[0]
        except OverflowError:
            return 0x7F800000 if x > 0 else 0xFF800000
    return x & 0xFFFFFFFF


def b64(x):
    if isinstance(x, float):
        try:
            return struct.unpack(">Q", struct.pack(">d", x))[0]
        except OverflowError:
            return 0x7FF0000000000000 if x > 0 else 0xFFF0000000000000
    return x & 0xFFFFFFFFFFFFFFFF


def s32(bits):
    return bits - (1 << 32) if bits >= (1 << 31) else bits


def s64(bits):
    return bits - (1 << 64) if bits >= (1 << 63) else bits


def canon(x, w):
    """Canonicalise a NaN result the way Winch's maybe_canonicalize_nan does."""
    if math.isnan(x):
        return CAN32 if w == 32 else CAN64
    return x


def wasm_min(x, y):
    # WebAssembly fmin: NaN if either is NaN; -0 < +0; otherwise the smaller
    if math.isnan(x) or math.isnan(y):
        return float("nan")
    if x == 0.0 and y == 0.0:
        return x if math.copysign(1.0, x) < 0 else y
    return x if x < y else y


def wasm_max(x, y):
    if math.isnan(x) or math.isnan(y):
        return float("nan")
    if x == 0.0 and y == 0.0:
        return x if math.copysign(1.0, x) > 0 else y
    return x if x > y else y


def float_round(x, mode):
    """ceil/floor/trunc/nearest with signed-zero preservation and NaN/Inf passthrough."""
    if math.isnan(x) or math.isinf(x) or x == 0.0:
        return x
    r = {"ceil": math.ceil, "floor": math.floor, "trunc": math.trunc}[mode](x)
    if r == 0:
        return -0.0 if math.copysign(1.0, x) < 0 else 0.0
    return float(r)


def nearest(x):
    """roundTiesToEven, signed zero preserved."""
    if math.isnan(x) or math.isinf(x) or x == 0.0:
        return x
    r = float(round(x))  # Python's round() on a float is round-half-to-even
    if r == 0:
        return -0.0 if math.copysign(1.0, x) < 0 else 0.0
    return r


def div(x, y, w):
    if math.isnan(x) or math.isnan(y):
        return float("nan")
    if math.isinf(x) and math.isinf(y):
        return float("nan")
    if x == 0.0 and y == 0.0:
        return float("nan")
    if y == 0.0:
        sign = math.copysign(1.0, x) * math.copysign(1.0, y)
        return math.inf if sign > 0 else -math.inf
    return x / y


def trunc_to_int(x, lo, hi):
    """`trunc(x)` as an int, or None when the conversion traps."""
    if math.isnan(x) or math.isinf(x):
        return None
    t = math.trunc(x)
    if lo <= t <= hi:
        return t
    return None


def sat(x, lo, hi):
    if math.isnan(x):
        return 0
    if x <= lo:
        return lo
    if x >= hi:
        return hi
    return math.trunc(x)


def to_float(n, w):
    """Integer → float, round-to-nearest-ties-to-even (C's conversion)."""
    return float(n)


W = {  # opcode → (format, kind)
    0x5B: (32, "eq"), 0x5C: (32, "ne"), 0x5D: (32, "lt"), 0x5E: (32, "gt"),
    0x5F: (32, "le"), 0x60: (32, "ge"),
    0x61: (64, "eq"), 0x62: (64, "ne"), 0x63: (64, "lt"), 0x64: (64, "gt"),
    0x65: (64, "le"), 0x66: (64, "ge"),
    0x8B: (32, "abs"), 0x8C: (32, "neg"), 0x8D: (32, "ceil"), 0x8E: (32, "floor"),
    0x8F: (32, "trunc"), 0x90: (32, "nearest"), 0x91: (32, "sqrt"),
    0x92: (32, "add"), 0x93: (32, "sub"), 0x94: (32, "mul"), 0x95: (32, "div"),
    0x96: (32, "min"), 0x97: (32, "max"), 0x98: (32, "copysign"),
    0x99: (64, "abs"), 0x9A: (64, "neg"), 0x9B: (64, "ceil"), 0x9C: (64, "floor"),
    0x9D: (64, "trunc"), 0x9E: (64, "nearest"), 0x9F: (64, "sqrt"),
    0xA0: (64, "add"), 0xA1: (64, "sub"), 0xA2: (64, "mul"), 0xA3: (64, "div"),
    0xA4: (64, "min"), 0xA5: (64, "max"), 0xA6: (64, "copysign"),
    0xA8: (32, "i32.trunc_s"), 0xA9: (32, "i32.trunc_u"),
    0xAA: (64, "i32.trunc_s"), 0xAB: (64, "i32.trunc_u"),
    0xAE: (32, "i64.trunc_s"), 0xAF: (32, "i64.trunc_u"),
    0xB0: (64, "i64.trunc_s"), 0xB1: (64, "i64.trunc_u"),
    0xB2: (32, "f32.convert_i32_s"), 0xB3: (32, "f32.convert_i32_u"),
    0xB4: (32, "f32.convert_i64_s"), 0xB5: (32, "f32.convert_i64_u"),
    0xB6: (64, "f32.demote_f64"),
    0xB7: (32, "f64.convert_i32_s"), 0xB8: (32, "f64.convert_i32_u"),
    0xB9: (32, "f64.convert_i64_s"), 0xBA: (32, "f64.convert_i64_u"),
    0xBB: (32, "f64.promote_f32"),
    0xBC: (32, "i32.reinterpret_f32"), 0xBD: (64, "i64.reinterpret_f64"),
    0xBE: (32, "f32.reinterpret_i32"), 0xBF: (64, "f64.reinterpret_i64"),
    0xFC00: (32, "i32.trunc_sat_f32_s"), 0xFC01: (32, "i32.trunc_sat_f32_u"),
    0xFC02: (64, "i32.trunc_sat_f64_s"), 0xFC03: (64, "i32.trunc_sat_f64_u"),
    0xFC04: (32, "i64.trunc_sat_f32_s"), 0xFC05: (32, "i64.trunc_sat_f32_u"),
    0xFC06: (64, "i64.trunc_sat_f64_s"), 0xFC07: (64, "i64.trunc_sat_f64_u"),
}

BOUNDS = {
    "i32.trunc_s": (-(2**31), 2**31 - 1), "i32.trunc_u": (0, 2**32 - 1),
    "i64.trunc_s": (-(2**63), 2**63 - 1), "i64.trunc_u": (0, 2**64 - 1),
}


def evaluate(op, a, b):
    """Return ('v', bits) or ('trap',)."""
    if op not in W:
        return ("badop",)
    w, kind = W[op]
    rd = f32 if w == 32 else f64
    # the encoding of the result follows the instruction's result type, which is not always the
    # operand format (`f64.convert_i32_s` takes an i32, `f32.demote_f64` an f64)
    wr = b64 if result_width(op) == 64 else b32
    x, y = rd(a), rd(b)
    if kind in ("eq", "ne", "lt", "gt", "le", "ge"):
        if math.isnan(x) or math.isnan(y):
            r = kind == "ne"
        else:
            r = {"eq": x == y, "ne": x != y, "lt": x < y, "gt": x > y,
                 "le": x <= y, "ge": x >= y}[kind]
        return ("v", 1 if r else 0)
    if kind == "abs":
        return ("v", a & (0x7FFFFFFF if w == 32 else 0x7FFFFFFFFFFFFFFF))
    if kind == "neg":
        return ("v", (a ^ (0x80000000 if w == 32 else 0x8000000000000000)) & (0xFFFFFFFF if w == 32 else 0xFFFFFFFFFFFFFFFF))
    if kind in ("ceil", "floor", "trunc", "nearest"):
        return ("v", wr(canon(float_round(x, kind) if kind != "nearest" else nearest(x), w)))
    if kind == "sqrt":
        if math.isnan(x):
            return ("v", CAN32 if w == 32 else CAN64)
        if x < 0:
            return ("v", CAN32 if w == 32 else CAN64)
        return ("v", wr(math.sqrt(x)))
    if kind in ("add", "sub", "mul", "div", "min", "max", "copysign"):
        if kind == "copysign":
            sb = a & (0x80000000 if w == 32 else 0x8000000000000000)
            ab = a & (0x7FFFFFFF if w == 32 else 0x7FFFFFFFFFFFFFFF)
            nb = b & (0x80000000 if w == 32 else 0x8000000000000000)
            return ("v", (ab | nb) & (0xFFFFFFFF if w == 32 else 0xFFFFFFFFFFFFFFFF))
        if kind == "add":
            r = x + y
        elif kind == "sub":
            r = x - y
        elif kind == "mul":
            r = x * y
        elif kind == "div":
            r = div(x, y, w)
        elif kind == "min":
            r = wasm_min(x, y)
        else:
            r = wasm_max(x, y)
        if math.isnan(r):
            return ("v", CAN32 if w == 32 else CAN64)
        return ("v", wr(r))
    if kind.startswith("i32.trunc_") and "sat" not in kind:
        lo, hi = BOUNDS[kind]
        t = trunc_to_int(x, lo, hi)
        return ("trap",) if t is None else ("v", t & 0xFFFFFFFF)
    if kind.startswith("i64.trunc_") and "sat" not in kind:
        lo, hi = BOUNDS[kind]
        t = trunc_to_int(x, lo, hi)
        return ("trap",) if t is None else ("v", t & 0xFFFFFFFFFFFFFFFF)
    if "trunc_sat" in kind:
        # i32.trunc_sat_f32_s → the saturating form of i32.trunc_f32_s
        base = kind.replace("_sat", "").replace("_f32", "").replace("_f64", "")
        lo, hi = BOUNDS[base]
        r = sat(x, lo, hi)
        width = 32 if base.startswith("i32") else 64
        return ("v", r & (0xFFFFFFFF if width == 32 else 0xFFFFFFFFFFFFFFFF))
    if kind == "f32.convert_i32_s":
        return ("v", wr(to_float(s32(a), 32)))
    if kind == "f32.convert_i32_u":
        return ("v", wr(to_float(a & 0xFFFFFFFF, 32)))
    if kind == "f32.convert_i64_s":
        return ("v", wr(to_float(s64(a), 32)))
    if kind == "f32.convert_i64_u":
        return ("v", wr(to_float(a & 0xFFFFFFFFFFFFFFFF, 32)))
    if kind == "f64.convert_i32_s":
        return ("v", wr(to_float(s32(a), 64)))
    if kind == "f64.convert_i32_u":
        return ("v", wr(to_float(a & 0xFFFFFFFF, 64)))
    if kind == "f64.convert_i64_s":
        return ("v", wr(to_float(s64(a), 64)))
    if kind == "f64.convert_i64_u":
        return ("v", wr(to_float(a & 0xFFFFFFFFFFFFFFFF, 64)))
    if kind == "f32.demote_f64":
        if math.isnan(x):
            return ("v", CAN32)
        return ("v", b32(x))
    if kind == "f64.promote_f32":
        if math.isnan(x):
            return ("v", CAN64)
        return ("v", b64(x))
    if kind == "i32.reinterpret_f32":
        return ("v", a & 0xFFFFFFFF)
    if kind == "i64.reinterpret_f64":
        return ("v", a & 0xFFFFFFFFFFFFFFFF)
    if kind == "f32.reinterpret_i32":
        return ("v", a & 0xFFFFFFFF)
    if kind == "f64.reinterpret_i64":
        return ("v", a & 0xFFFFFFFFFFFFFFFF)
    return ("badop",)


def result_width(op):
    """Width of the result, per `NearSpecV3.Wasm.floatResultType`."""
    if 0x5B <= op <= 0x66:
        return 32
    if 0x8B <= op <= 0x98:
        return 32
    if 0x99 <= op <= 0xA6:
        return 64
    if op <= 0xAB:
        return 32
    if op <= 0xB1:
        return 64
    if op <= 0xB6:
        return 32
    if op <= 0xBB:
        return 64
    if op == 0xBC:
        return 32
    if op == 0xBD:
        return 64
    if op == 0xBE:
        return 32
    if op == 0xBF:
        return 64
    if op <= 0xFC03:
        return 32
    return 64


def fmt(op, res):
    if res[0] == "trap":
        return "trap"
    if res[0] == "badop":
        return "badop"
    w = result_width(op)
    return "%0*x" % (w // 4, res[1])


def main():
    for line in sys.stdin:
        parts = line.split()
        if len(parts) != 3:
            print("badline")
            continue
        op, a, b = int(parts[0]), int(parts[1], 16), int(parts[2], 16)
        print(fmt(op, evaluate(op, a, b)))


if __name__ == "__main__":
    main()
