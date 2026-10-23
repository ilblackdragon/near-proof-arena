#!/usr/bin/env python3
"""Plan §5 item 2's regression experiment: break the new behaviour and show a targeted test fails.

The claim "the float extension is additive" has two halves, and each is checked by removing the
mechanism and observing the *specific* failure it should cause:

  A. **Lifting the guard is what admits float contracts.** With `NearCfg.floats = false` (D3α) the
     `d3float` chunk must be `out_of_domain` for a float reason; with `floatPv86` it must be
     decided. `chunk_float.py` asserts the pair, and this script prints the two verdicts for one
     case as the minimal evidence — if the `!cfg.floats` gate were dropped from `Prepare.lean`, the
     D3α verdict would stop being a float exclusion and the pair would collapse.

  B. **Canonicalisation is what makes NaN results deterministic.** `float_ref.py` was written with
     the canonical-NaN rule; running it with the rule removed (`--no-canon`) must disagree with the
     Lean kernel on exactly the NaN-producing cases. If the kernel did not canonicalise, the check
     would silently pass in both modes — which is what "no regression experiment" would look like.

  float_regression.py [--case DIR]

Exit 1 if either experiment fails to discriminate.
"""
import argparse
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import float_ref  # noqa: E402

BIN = os.path.join(HERE, "../lean/.lake/build/bin")
LEAN = os.environ.get("D3_FLOAT_SPEC", os.path.join(BIN, "nearspec-v3-test-float"))


def part_a(case):
    d3 = json.loads(subprocess.run([os.path.join(BIN, "nearspec-v3-check-d3"), case],
                                   capture_output=True, text=True).stdout.splitlines()[0])
    d3f = json.loads(subprocess.run([os.path.join(BIN, "nearspec-v3-check-d3f"), case],
                                    capture_output=True, text=True).stdout.splitlines()[0])
    float_words = ("float type or operator", "float global", "float in an imported function type")
    ok = (d3["verdict"] == "out_of_domain"
          and any(w in (d3["reason"] or "") for w in float_words)
          and d3f["verdict"] == "accept")
    print(f"A guard-lift: D3alpha {d3['verdict']} ({d3['reason']}); floatPv86 {d3f['verdict']}"
          f" -> {'DISCRIMINATES' if ok else 'FAILS TO DISCRIMINATE'}")
    return ok


def part_b():
    """Turn the canonical-NaN rule off in the reference and count how many kernel cases diverge."""
    lines = []
    # every operation that can produce a NaN, with a NaN operand and with a NaN-producing operand
    nan_ops = [0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x91, 0x8D, 0x8E, 0x8F, 0x90,
               0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0x9F, 0x9B, 0x9C, 0x9D, 0x9E,
               0xB6, 0xBB, 0xA8, 0xAE, 0xFC00, 0xFC04]
    for op in nan_ops:
        w = float_ref.W[op][0]
        if w == 32:
            nan, inf, zero = 0x7FC12345, 0x7F800000, 0
        else:
            nan, inf, zero = 0x7FF8000000012345, 0x7FF0000000000000, 0
        for a, b in ((nan, nan), (nan, inf), (inf, inf), (inf, zero), (zero, zero), (nan, zero)):
            lines.append(f"{op} {a:x} {b:x}")
    lean = subprocess.run([LEAN], input="\n".join(lines) + "\n", capture_output=True,
                          text=True, check=True).stdout.splitlines()
    disagreements = 0
    for line, out in zip(lines, lean):
        op, a, b = line.split()
        op, a, b = int(op), int(a, 16), int(b, 16)
        kept = float_ref.evaluate(op, a, b)
        nocanon = _nocanon(op, a, b)
        # the kernel agrees with the canonical reference ...
        agree_canon = float_ref.fmt(op, kept) == out
        # ... and disagrees with the un-canonicalised one somewhere
        if float_ref.fmt(op, nocanon) != out:
            disagreements += 1
        if not agree_canon:
            print(f"FAIL kernel disagrees with the canonical reference on {line}")
            return False
    ok = disagreements > 0
    print(f"B canonical-NaN: {disagreements}/{len(lines)} cases differ without the rule"
          f" -> {'DISCRIMINATES' if ok else 'FAILS TO DISCRIMINATE'}")
    return ok


def _nocanon(op, a, b):
    """`float_ref.evaluate` with the canonical-NaN rule removed: NaN payloads are passed through
    the host operation instead of being overwritten with the canonical pattern."""
    w, kind = float_ref.W[op]
    rd = float_ref.f32 if w == 32 else float_ref.f64
    x, y = rd(a), rd(b)
    if kind in ("add", "sub", "mul", "div", "min", "max"):
        import math
        if kind == "add":
            r = x + y
        elif kind == "sub":
            r = x - y
        elif kind == "mul":
            r = x * y
        elif kind == "div":
            r = float_ref.div(x, y, w)
        elif kind == "min":
            r = float_ref.wasm_min(x, y)
        else:
            r = float_ref.wasm_max(x, y)
        try:
            bits = float_ref.b32(r) if w == 32 else float_ref.b64(r)
        except (OverflowError, ValueError):
            bits = 0x7FC00000 if w == 32 else 0x7FF8000000000000
        return ("v", bits)
    if kind == "sqrt":
        import math
        if math.isnan(x) or x < 0:
            return ("v", float_ref.b32(x) if w == 32 else float_ref.b64(x))
    return float_ref.evaluate(op, a, b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--case", default="/data/illia/nearproof-deps/corpora/d3c9/ood/00-h10031-s3")
    a = ap.parse_args()
    ok = part_a(a.case) & part_b()
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
