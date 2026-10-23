#!/usr/bin/env python3
"""L2 float differential test: the Lean IEEE kernel vs an independent Python IEEE reference.

  difftest_float.py [--cases N] [--seed S] [--nearcore]

Families (each with directed edge values plus generated cases):
  * every float opcode with no immediates that `NearSpecV3.Wasm.isFloatOpNoImm` accepts —
    arithmetic, `abs/neg/sqrt/ceil/floor/trunc/nearest`, comparisons, conversions, saturating
    truncations, reinterprets, `demote`/`promote`;
  * directed edge values per family: signed zeros, subnormals, the subnormal/normal boundary,
    infinities, canonical and non-canonical NaNs (both signs), rounding ties in the last bit,
    conversion boundaries (2^31, 2^32-1, 2^63, 2^64-1 and one step past each), trap boundaries.

With `--nearcore`, an equally sized subsample is additionally executed by pinned nearcore's own
engine through `oracle/wasm-d3` (a real Wasm module per opcode, real instrumented gas): see
`float_nearcore.py`. Without it, the reference is the Python statement of IEEE plus the two rules
nearcore's engine configuration fixes (canonical NaNs; bit-preserving abs/neg/copysign/reinterpret).

Exit 1 on any disagreement.
"""
import argparse
import random
import subprocess
import sys

HERE = __import__("os").path.dirname(__import__("os").path.abspath(__file__))
sys.path.insert(0, HERE)
import float_ref  # noqa: E402

LEAN = __import__("os").environ.get(
    "D3_FLOAT_SPEC", __import__("os").path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-test-float"))

BIN = {32: 0xFFFFFFFF, 64: 0xFFFFFFFFFFFFFFFF}
SIGN = {32: 0x80000000, 64: 0x8000000000000000}
EXP = {32: 0x7F800000, 64: 0x7FF0000000000000}
CAN = {32: 0x7FC00000, 64: 0x7FF8000000000000}


def edge32():
    v = [
        0x00000000, 0x80000000,          # ±0
        0x00000001, 0x80000001,          # ±min subnormal
        0x007FFFFF, 0x807FFFFF,          # ±max subnormal
        0x00800000, 0x80800000,          # ±min normal
        0x3F800000, 0xBF800000,          # ±1
        0x3F000000, 0xBF000000,          # ±0.5
        0x40000000, 0xC0000000,          # ±2
        0x7F7FFFFF, 0xFF7FFFFF,          # ±max finite
        0x7F800000, 0xFF800000,          # ±inf
        0x7FC00000, 0xFFC00000,          # ±canonical qNaN
        0x7FC12345, 0xFFC12345,          # ±qNaN with a payload
        0x7F800001, 0xFF800001,          # ±signalling NaN
        0x4B000000, 0x4B7FFFFF,          # 2^23, 2^23-1 (integer boundary)
        0x4EFFFFFF,                      # just below 2^31
        0x4F000000, 0xCF000000,          # ±2^31
        0x4F800000,                      # 2^32
        0x5F000000, 0xDF000000,          # ±2^63
        0x5F800000,                      # 2^64
        0x3FC00000, 0x40200000,          # 1.5, 2.5
        0x33800000,                      # 2^-24
        0x34000000,                      # 2^-23
    ]
    return v


def edge64():
    return [
        0x0000000000000000, 0x8000000000000000,
        0x0000000000000001, 0x8000000000000001,
        0x000FFFFFFFFFFFFF, 0x800FFFFFFFFFFFFF,
        0x0010000000000000, 0x8010000000000000,
        0x3FF0000000000000, 0xBFF0000000000000,
        0x3FE0000000000000, 0x4000000000000000,
        0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF,
        0x7FF0000000000000, 0xFFF0000000000000,
        0x7FF8000000000000, 0xFFF8000000000000,
        0x7FF8000000012345, 0xFFF8000000012345,
        0x7FF0000000000001, 0xFFF0000000000001,
        0x4330000000000000,              # 2^52
        0x43E0000000000000, 0xC3E0000000000000,  # ±2^63
        0x43F0000000000000,              # 2^64
        0x41E0000000000000,              # 2^31
        0x3FF8000000000000,              # 1.5
        0x4004000000000000,              # 2.5
    ]


def ops_for(w):
    """Float opcodes with operand format `w` (see `float_ref.W`)."""
    out = []
    for op, (fw, kind) in float_ref.W.items():
        if kind in ("i32.reinterpret_f32", "f32.reinterpret_i32"):
            out.append(op) if w == 32 else None
        elif kind in ("i64.reinterpret_f64", "f64.reinterpret_i64"):
            out.append(op) if w == 64 else None
        elif fw != w:
            continue
        else:
            out.append(op)
    return sorted(out)


def gen(cases, seed):
    rng = random.Random(seed)
    lines, labels = [], []
    e32, e64 = edge32(), edge64()
    for op in sorted(float_ref.W):
        w = float_ref.W[op][0]
        edges = e32 if w == 32 else e64
        # directed: every ordered pair of edge values (unary ops ignore b)
        for a in edges:
            for b in edges:
                lines.append(f"{op} {a:x} {b:x}")
                labels.append(f"edge op=0x{op:x} a={a:x} b={b:x}")
        # generated: random pairs with a bias towards exponent-field neighbours
        n = cases
        for _ in range(n):
            pair = []
            for _i in range(2):
                r = rng.random()
                if r < 0.5:
                    pair.append(rng.getrandbits(w))
                elif r < 0.75:
                    # random-ish value with a small exponent (normal or subnormal)
                    pair.append(rng.getrandbits(w - 9) | (rng.randrange(0, 8) << (w - 9)))
                else:
                    # neighbour of an edge value
                    base = rng.choice(edges)
                    pair.append((base + rng.randrange(-4, 5)) & BIN[w])
            lines.append(f"{op} {pair[0]:x} {pair[1]:x}")
            labels.append(f"rand op=0x{op:x} a={pair[0]:x} b={pair[1]:x}")
    return lines, labels


def run_lean(lines):
    p = subprocess.run([LEAN], input="\n".join(lines) + "\n", capture_output=True, text=True,
                       check=True)
    return p.stdout.splitlines()


def run_py(lines):
    out = []
    for l in lines:
        op, x, y = _parse(l)
        out.append(float_ref.fmt(op, float_ref.evaluate(op, x, y)))
    return out


def _parse(line):
    op, a, b = line.split()
    return int(op), int(a, 16), int(b, 16)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=4, help="generated cases per opcode")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--nearcore", action="store_true", help="also diff a sample against nearcore")
    a = ap.parse_args()
    lines, labels = gen(a.cases, a.seed)
    lean = run_lean(lines)
    py = run_py(lines)
    bad = 0
    for i, (x, y) in enumerate(zip(lean, py)):
        if x != y:
            bad += 1
            if bad <= 20:
                print(f"DISAGREE {labels[i]}: lean {x} python {y}")
    print(f"family=float cases={len(lines)} opcodes={len(set(float_ref.W))} disagreements={bad}")
    if a.nearcore:
        import float_nearcore
        nb = float_nearcore.compare(lines, labels, sample=400, seed=a.seed)
        print(f"nearcore_sample disagreements={nb}")
        bad += nb
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
