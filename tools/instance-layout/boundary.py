#!/usr/bin/env python3
"""Instance-layout boundary per architecture (workplan item 12).

For the three module shapes of the `runtime-errors` family (`oracle/v3-successor/src/rterr.rs`,
`SHAPE_A/B/C`), binary-search the largest defined-global count whose NEAR-prepared module still
fits Wasmtime's pooling allocator, using `instance-layout-probe` (this crate) as the judge.

Preparation is done by the pinned harness (`near-wasm-d3-harness prepare`, nearcore's own
`prepare_contract`), on x86_64; it is a pure wasm transform. The probe is then run natively
(x86_64, Winch) and, with `--runner`, under an emulator for another architecture (aarch64,
Cranelift).

Usage: boundary.py --harness H --probe P [--runner "qemu-aarch64-static"] [--out FILE]
"""
import argparse
import json
import os
import shlex
import subprocess
import sys
import tempfile

SHAPES = {
    # name: (host_imports, writes, extra_exports, elems)
    "a": ([], True, 0, 0),
    "b": ([("input", "(param i64)"), ("value_return", "(param i64 i64)"),
           ("log_utf8", "(param i64 i64)"), ("panic", "")], True, 30, 40),
    "c": ([], False, 0, 0),
}
# x86_64 boundaries measured with pinned nearcore (docs/evidence/lean-chunk-completion/runtime-errors/boundary.json).
X86_FIT = {"a": 65501, "b": 65344, "c": 65505}


def shape_wat(shape, globals_):
    """Port of `rterr::shape_wat` (no unknown import)."""
    host_imports, writes, extra_exports, elems = SHAPES[shape]
    w = ["(module"]
    if writes:
        w.append('  (import "env" "storage_write" (func $sw (param i64 i64 i64 i64 i64) (result i64)))')
    for i, (name, sig) in enumerate(host_imports):
        w.append(f'  (import "env" "{name}" (func $h{i} {sig}))')
    w.append('  (memory 1)\n  (data (i32.const 0) "kv")')
    for i in range(globals_):
        w.append(f"  (global $g{i} i32 (i32.const {i & 0xff}))")
    if writes:
        w.append('  (func (export "main") (drop (call $sw (i64.const 1) (i64.const 0) (i64.const 1) (i64.const 1) (i64.const 0))))')
    else:
        w.append('  (func (export "main"))')
    for i in range(extra_exports):
        w.append(f'  (func (export "x{i}"))')
    if elems:
        for i in range(elems):
            w.append(f"  (func $e{i})")
        w.append(f"  (table {elems} funcref)")
        w.append("  (elem (i32.const 0) func" + "".join(f" $e{i}" for i in range(elems)) + ")")
    w.append(")")
    return "\n".join(w) + "\n"


class Judge:
    def __init__(self, harness, probe, runner):
        self.harness, self.probe, self.runner = harness, probe, runner
        self.tmp = tempfile.mkdtemp(prefix="layout-")
        self.cache = {}

    def prepared_hex(self, shape, n):
        wat = os.path.join(self.tmp, "m.wat")
        wasm = os.path.join(self.tmp, "m.wasm")
        with open(wat, "w") as f:
            f.write(shape_wat(shape, n))
        subprocess.run(["wasm-tools", "parse", wat, "-o", wasm], check=True)
        code = open(wasm, "rb").read().hex()
        out = subprocess.run([self.harness, "prepare"], input=f"300000000000000 {code}\n",
                             capture_output=True, text=True, check=True).stdout.strip()
        if out.startswith("prepare-error"):
            raise SystemExit(f"shape {shape} n={n}: {out}")
        return out

    def fits(self, shape, n):
        if (shape, n) in self.cache:
            return self.cache[(shape, n)]
        hx = self.prepared_hex(shape, n)
        cmd = (shlex.split(self.runner) if self.runner else []) + [self.probe]
        p = subprocess.run(cmd, input=hx + "\n", capture_output=True, text=True, check=True)
        line = p.stdout.strip()
        if line == "fit":
            r = (True, line)
        elif line.startswith("over"):
            r = (False, line)
        else:
            raise SystemExit(f"unexpected probe output for {shape} n={n}: {line!r} {p.stderr}")
        self.cache[(shape, n)] = r
        self.banner = p.stderr.strip()
        return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--harness", required=True)
    ap.add_argument("--probe", required=True)
    ap.add_argument("--runner", default="")
    ap.add_argument("--lo", type=int, default=60000)
    ap.add_argument("--hi", type=int, default=70000)
    ap.add_argument("--out")
    a = ap.parse_args()
    j = Judge(a.harness, a.probe, a.runner)
    res = {}
    for shape in SHAPES:
        lo, hi = a.lo, a.hi
        assert j.fits(shape, lo)[0], f"{shape}: lo={lo} does not fit"
        assert not j.fits(shape, hi)[0], f"{shape}: hi={hi} fits"
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if j.fits(shape, mid)[0]:
                lo = mid
            else:
                hi = mid
        res[shape] = {"fit": lo, "over": hi, "over_outcome": j.fits(shape, hi)[1],
                      "x86_64_nearcore_fit": X86_FIT[shape], "equal_to_x86_64": lo == X86_FIT[shape]}
        print(shape, res[shape], flush=True)
    doc = {"probe": j.banner, "runner": a.runner or None, "shapes": res}
    if a.out:
        with open(a.out, "w") as f:
            json.dump(doc, f, indent=1)
            f.write("\n")
    print(json.dumps(doc, indent=1))


if __name__ == "__main__":
    sys.exit(main())
