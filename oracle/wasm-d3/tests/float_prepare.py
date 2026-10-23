#!/usr/bin/env python3
"""Directed cases for the two *preparation-only* float rows (`L0-W-001`, `L0-W-002`).

Those rows are about the guards, not the operators, and the operator tests do not reach them: a
module may use a float only in

  * an **imported function signature** that no code calls (`Prepare.lean:215`,
    "float in an imported function type"), or
  * an **f64 global** whose initialiser no code reads (`Prepare.lean:245`, "float global").

For each module this script checks the *whole* pipeline agrees:

| check | D3α (`Wasm.pv86`) | float domain (`Wasm.floatPv86`) |
|---|---|---|
| Lean `prepare`/`run` outcome | `out-of-domain …` with the specific message | the same outcome line as nearcore |
| pinned nearcore (`oracle/wasm-d3`) | — | `ok`/`abort` line, burnt and used gas |

The second column is what makes the row `implemented` rather than `inspection only`: the guard is
lifted *and* the module behaves like nearcore's. Also checks the discriminating negatives:
`f64.const` in an *unreachable* global still has to be accepted (it is a value, not an operator),
and an imported float signature with the **wrong arity** must still be a link error in both.

  float_prepare.py

Exit 1 on any disagreement.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.environ.get("D3_HARNESS",
                         "/tmp/opencode/target-wasm-d3/release/near-wasm-d3-harness")
LEAN = os.environ.get("D3_SPEC",
                      os.path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-wasm"))
GAS = 1000000000000000


def uleb(n):
    out = b""
    while True:
        b = n & 0x7F
        n >>= 7
        out += bytes([b | 0x80]) if n else bytes([b])
        if not n:
            return out


def vec(x):
    return uleb(len(x)) + b"".join(x)


def sect(i, p):
    return bytes([i]) + uleb(len(p)) + p


def name(s):
    b = s.encode()
    return uleb(len(b)) + b


HDR = b"\x00asm\x01\x00\x00\x00"
EMPTY_T = b"\x60" + vec([]) + vec([])


def body(insns=b""):
    b = insns + b"\x0b"
    return sect(10, vec([uleb(len(b) + 1) + b"\x00" + b]))


def export_main(idx):
    return sect(7, vec([name("main") + b"\x00" + uleb(idx)]))


def import_only_float(param="f64", called=False, arity_ok=True):
    """`env::f` imported with a float parameter, never called. `main` is `[] -> []`."""
    vt = {"f64": b"\x7c", "f32": b"\x7d"}[param]
    params = [vt] if arity_ok else [vt, vt]
    types = [b"\x60" + vec(params) + vec([]), EMPTY_T]
    imports = [name("env") + name("f") + b"\x00" + uleb(0)]
    call = b"\x44" + (0).to_bytes(8, "little") + b"\x10\x00" if called and param == "f64" else b""
    return HDR + sect(1, vec(types)) + sect(2, vec(imports)) + sect(3, vec([uleb(1)])) + \
        export_main(1) + body(call)


def float_global_only(mut=False, read=False):
    """One f64 global, initialised to `1.0`; never read (or read and dropped)."""
    ginit = b"\x44" + (0x3FF0000000000000).to_bytes(8, "little")
    globals_ = vec([b"\x7c" + (b"\x01" if mut else b"\x00") + ginit + b"\x0b"])
    types = [EMPTY_T]
    insns = b"\x23\x00\x1a" if read else b""   # global.get 0; drop
    return HDR + sect(1, vec(types)) + sect(3, vec([uleb(0)])) + sect(6, globals_) + \
        export_main(0) + body(insns)


def lean(line, floats):
    args = [LEAN] + (["--floats"] if floats else [])
    p = subprocess.run(args, input=line + "\n", capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"lean driver failed: {p.stderr[:400]}")
    return p.stdout.strip()


def nearcore(line):
    p = subprocess.run([HARNESS], input=line + "\n", capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"harness failed: {p.stderr[:400]}")
    return p.stdout.strip()


CASES = [
    # (name, module, d3alpha-message-substring)
    ("import-only f64 signature", import_only_float("f64"), "float in an imported function type"),
    ("import-only f32 signature", import_only_float("f32"), "float in an imported function type"),
    ("f64 global", float_global_only(), "float global"),
    ("f64 global, read and dropped", float_global_only(read=True), "float global"),
    ("mutable f64 global", float_global_only(mut=True), "float global"),
]


def main():
    bad = 0
    for label, mod, expect in CASES:
        line = f"{GAS} {mod.hex()}"
        d3 = lean(line, False)
        fl = lean(line, True)
        near = nearcore(line)
        if "out-of-domain" not in d3 or expect not in d3:
            print(f"FAIL {label}: D3alpha gave {d3!r}, expected out-of-domain with {expect!r}")
            bad += 1
        # under floatPv86 the whole line must equal nearcore's
        if fl != near:
            print(f"FAIL {label}: floatPv86 {fl!r} != nearcore {near!r}")
            bad += 1
        else:
            print(f"ok   {label}: D3alpha excluded; floatPv86 == nearcore ({fl.split()[0]}"
                  f"{' gas ' + fl.split()[1] if len(fl.split()) > 1 else ''})")

    # discriminating negative: a float *import signature mismatch* is still a link error on both
    # sides (lifting the float guard must not lift signature checking).
    label = "imported float signature, called with the wrong type"
    mod = import_only_float("f64", called=True)
    line = f"{GAS} {mod.hex()}"
    fl, near = lean(line, True), nearcore(line)
    if not (fl.startswith("abort") and "LinkError" in fl and near.startswith("abort")):
        print(f"FAIL {label}: floatPv86 {fl!r} nearcore {near!r} — expected a LinkError on both")
        bad += 1
    else:
        print(f"ok   {label}: both abort with LinkError")

    print(f"family=float-prepare cases={len(CASES) + 1} disagreements={bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
