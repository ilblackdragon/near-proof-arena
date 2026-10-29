#!/usr/bin/env python3
"""UQ-003 / item 12: float results, NaN sign and payload included, under nearcore's Wasmtime engine
configuration on each target (x86_64 -> Winch, aarch64 -> Cranelift; `wasmtime_runner/mod.rs:512-534`).

Builds one module exporting every float operator Wasmtime canonicalises (add, sub, mul, div, min,
max, sqrt, ceil, floor, trunc, nearest, promote, demote) plus the bitwise ones it does not (abs,
neg, copysign), each taking and returning raw bit patterns, and calls it on every operand pair from
a fixed set of specials (signed quiet/signalling NaNs with and without payload, infinities, signed
zeros, subnormals, extremes, halves). Every result is also checked against the rule stated for B3 in
`docs/research/near-wasm-boundary.md`: a NaN result of a canonicalised operator is the positive
canonical NaN. Two probes (native and emulated) must agree bit for bit.

Usage: nan_probe.py --probe P [--runner R] [--other-probe P2 --other-runner R2] [--out FILE]
"""
import argparse
import json
import shlex
import subprocess
import sys
import tempfile
import os

F32 = [0x7FC00000, 0xFFC00000, 0x7FC12345, 0xFFC12345, 0x7F800001, 0xFF800001, 0x7FBFFFFF,
       0x7F800000, 0xFF800000, 0x00000000, 0x80000000, 0x3F800000, 0xBF800000, 0x00000001,
       0x80000001, 0x7F7FFFFF, 0x40200000, 0xC0200000, 0x3F000000, 0xBF000000]
F64 = [0x7FF8000000000000, 0xFFF8000000000000, 0x7FF8000000012345, 0xFFF8000000012345,
       0x7FF0000000000001, 0xFFF0000000000001, 0x7FF7FFFFFFFFFFFF, 0x7FF0000000000000,
       0xFFF0000000000000, 0x0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000,
       0x1, 0x8000000000000001, 0x7FEFFFFFFFFFFFFF, 0x4004000000000000, 0xC004000000000000,
       0x3FE0000000000000, 0xBFE0000000000000]
BIN = ["add", "sub", "mul", "div", "min", "max", "copysign"]
UN = ["sqrt", "ceil", "floor", "trunc", "nearest", "abs", "neg"]
CANON = {"add", "sub", "mul", "div", "min", "max", "sqrt", "ceil", "floor", "trunc", "nearest",
         "promote", "demote"}
IT = {"f32": "i32", "f64": "i64"}


def module_wat():
    w = ["(module"]
    for t in ("f32", "f64"):
        i = IT[t]
        for op in BIN:
            w.append(f'(func (export "{t}.{op}") (param {i} {i}) (result {i}) '
                     f'local.get 0 {t}.reinterpret_{i} local.get 1 {t}.reinterpret_{i} {t}.{op} {i}.reinterpret_{t})')
        for op in UN:
            w.append(f'(func (export "{t}.{op}") (param {i}) (result {i}) '
                     f'local.get 0 {t}.reinterpret_{i} {t}.{op} {i}.reinterpret_{t})')
    w.append('(func (export "f64.promote") (param i32) (result i64) local.get 0 f32.reinterpret_i32 f64.promote_f32 i64.reinterpret_f64)')
    w.append('(func (export "f32.demote") (param i64) (result i32) local.get 0 f64.reinterpret_i64 f32.demote_f64 i32.reinterpret_f32)')
    w.append(")")
    return "\n".join(w) + "\n"


def calls():
    out = []
    for t, vals in (("f32", F32), ("f64", F64)):
        for op in BIN:
            out += [f"{t}.{op} {a} {b}" for a in vals for b in vals]
        for op in UN:
            out += [f"{t}.{op} {a}" for a in vals]
    out += [f"f64.promote {a}" for a in F32]
    out += [f"f32.demote {a}" for a in F64]
    return out


def is_nan(bits, width):
    if width == 32:
        return (bits & 0x7F800000) == 0x7F800000 and (bits & 0x007FFFFF) != 0
    return (bits & 0x7FF0000000000000) == 0x7FF0000000000000 and (bits & 0x000FFFFFFFFFFFFF) != 0


def run(probe, runner, wasm_hex, lines):
    cmd = (shlex.split(runner) if runner else []) + [probe, "call"]
    p = subprocess.run(cmd, input=wasm_hex + "\n" + "\n".join(lines) + "\n", capture_output=True,
                       text=True, check=True)
    res = {}
    for ln in p.stdout.splitlines():
        lhs, rhs = ln.split(" -> ")
        res[lhs] = int(rhs)
    assert len(res) == len(lines), (len(res), len(lines))
    return res


def check_rule(res):
    bad = []
    for call, r in res.items():
        name = call.split()[0]
        t, op = name.split(".")
        width = 32 if t == "f32" else 64
        if op in CANON and is_nan(r, width):
            canon = 0x7FC00000 if width == 32 else 0x7FF8000000000000
            if r != canon:
                bad.append((call, hex(r)))
    return bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--probe", required=True)
    ap.add_argument("--runner", default="")
    ap.add_argument("--other-probe")
    ap.add_argument("--other-runner", default="")
    ap.add_argument("--out")
    ap.add_argument("--write-calls", help="write the call list (input of LeanFloat.lean)")
    ap.add_argument("--lean-results", help="output of LeanFloat.lean on the call list")
    a = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        wat = os.path.join(tmp, "f.wat")
        wasm = os.path.join(tmp, "f.wasm")
        open(wat, "w").write(module_wat())
        subprocess.run(["wasm-tools", "parse", wat, "-o", wasm], check=True)
        wasm_hex = open(wasm, "rb").read().hex()
    lines = calls()
    res = run(a.probe, a.runner, wasm_hex, lines)
    doc = {"calls": len(lines), "rule_violations": check_rule(res),
           "nan_results": sum(1 for c, r in res.items() if is_nan(r, 32 if c.startswith("f32") else 64))}
    if a.other_probe:
        other = run(a.other_probe, a.other_runner, wasm_hex, lines)
        diff = [(c, hex(res[c]), hex(other[c])) for c in lines if res[c] != other[c]]
        doc["other_rule_violations"] = check_rule(other)
        doc["differences"] = diff
        doc["equal"] = not diff
    print(json.dumps({k: (v if not isinstance(v, list) else v[:20]) for k, v in doc.items()}, indent=1))
    if a.lean_results:
        lean = {}
        for ln in open(a.lean_results):
            lhs, rhs = ln.rstrip("\n").split(" -> ")
            lean[lhs] = int(rhs)
        assert set(lean) == set(lines), "Lean results do not cover the call set"
        ldiff = [(c, hex(res[c]), hex(lean[c])) for c in lines if res[c] != lean[c]]
        doc["lean_differences"] = ldiff
        doc["lean_equal"] = not ldiff
    if a.write_calls:
        open(a.write_calls, "w").write("\n".join(lines) + "\n")
    if a.out:
        json.dump(doc, open(a.out, "w"), indent=1)
    ok = (not doc["rule_violations"] and not doc.get("other_rule_violations")
          and doc.get("equal", True) and doc.get("lean_equal", True))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
