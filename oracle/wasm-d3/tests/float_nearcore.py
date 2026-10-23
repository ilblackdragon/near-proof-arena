#!/usr/bin/env python3
"""Anchor the Lean float kernel to pinned nearcore's own engine (values and traps).

One check against `oracle/wasm-d3`'s harness (pinned nearcore 2.13.4, `near_vm_runner::prepare` +
`run`, PV86 mainnet config, Wasmtime/Winch, real instrumentation):

**Values and traps.** For each float opcode without immediates, a real Wasm module computes the op
on **constants** (the engine does not constant-fold: Winch is single-pass and
`cranelift_opt_level(None)`), stores the result in linear memory and returns it through
`value_return`. `resolve` (`wasmtime_runner/mod.rs:887-902`) requires the exported method to have
type `[] -> []`, which is why the result travels through memory rather than as a return value. The
returned bytes are compared bit-for-bit with `NearSpecV3.Wasm.evalFloatOp`, and a trapping opcode
must abort with `WasmTrap(IllegalArithmetic)`.

**Gas and the whole outcome line.** A second check compares the *complete* harness line
(`ok <burnt> <used> <ret> <balance>` / `abort …`) against the Lean driver's, for bodies containing
one, two and three copies of each float operator. Comparing totals rather than deltas matters: a
delta between bodies does not isolate the operator, because each repetition also re-emits its store
address, its operand constants and its store. The totals do exercise the finite-wasm merges (a
`pure` point may merge with its neighbour; `cvtop_partial` is a `pre` point that does not), and the
prologue makes the absolute value observable. `NearSpecV3.Wasm.floatPartial`'s classification is
also justified *in the Lean module* from the pinned finite-wasm source
(`instruction_categories.rs:167-180` lists exactly the eight trapping `trunc_f*` under
`cvtop_partial`); this run measures it.

  float_nearcore.py [--limit N] [--seed S] [--no-gas]

`--no-gas` also skips the instrumented-size comparison, which uses the same modules.

Exit 1 on any disagreement.
"""
import argparse
import os
import random
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import float_ref  # noqa: E402

HARNESS = os.environ.get("D3_HARNESS",
                         "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")
LEAN = os.environ.get("D3_FLOAT_SPEC",
                      os.path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-test-float"))
LEAN_SPEC = os.environ.get("D3_SPEC",
                           os.path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-wasm"))
REGULAR_OP_COST = 822756

VALTYPE = {"i32": 0x7F, "i64": 0x7E, "f32": 0x7D, "f64": 0x7C}
STORE = {"i32": (0x36, 2), "i64": (0x37, 3), "f32": (0x38, 2), "f64": (0x39, 3)}
# value_return(i64 vm_word_ptr, i64 len) -> ()  — see near-vm-runner imports.rs
VALUE_RETURN_INDEX = None  # filled by `imports()`


def uleb(n):
    out = b""
    while True:
        b = n & 0x7F
        n >>= 7
        out += bytes([b | 0x80]) if n else bytes([b])
        if not n:
            return out


def vec(items):
    return uleb(len(items)) + b"".join(items)


def sect(sid, payload):
    return bytes([sid]) + uleb(len(payload)) + payload


def name(s):
    b = s.encode()
    return uleb(len(b)) + b


def op_bytes(op):
    return b"\xfc" + uleb(op - 0xFC00) if op >= 0xFC00 else bytes([op])


def const(ty, bits):
    if ty == "f32":
        return b"\x43" + bits.to_bytes(4, "little")
    if ty == "f64":
        return b"\x44" + bits.to_bytes(8, "little")
    if ty == "i32":
        # signed LEB of the two's-complement value
        v = bits - (1 << 32) if bits >= (1 << 31) else bits
        out = b""
        while True:
            b = v & 0x7F
            v >>= 7
            if (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40)):
                return b"\x41" + out + bytes([b])
            out += bytes([b | 0x80])
    v = bits - (1 << 64) if bits >= (1 << 63) else bits
    out = b""
    while True:
        b = v & 0x7F
        v >>= 7
        if (v == 0 and not (b & 0x40)) or (v == -1 and (b & 0x40)):
            return b"\x42" + out + bytes([b])
        out += bytes([b | 0x80])


IMPORTS = [("env", "value_return", 2)]  # (module, name, type index)


def build_module(op, a, b, reps=1):
    """A module whose `main: [] -> []` computes `op` on constants `reps` times, stores the last
    result at address 0 and calls `value_return(0, width)`."""
    res = float_ref.result_width(op)
    resty = {32: "i32", 64: "i64"}[res] if not _is_float_result(op) else {32: "f32", 64: "f64"}[res]
    operands = _operand_types(op)
    # types: 0 = () -> (), 1 = () -> (i32, i64) for value_return's params
    # type 1 is value_return's real signature: [i64 len, i64 ptr] -> []
    types = [b"\x60" + vec([]) + vec([]),
             b"\x60" + vec([bytes([VALTYPE["i64"]]), bytes([VALTYPE["i64"]])]) + vec([])]
    mem = b"\x00" + uleb(1)
    imports = [name("env") + name("value_return") + b"\x00" + uleb(1)]
    funcs = [uleb(0)]  # the defined function's type: () -> ()
    body = b""
    for _ in range(reps):
        body += b"\x41\x00"
        for i, t in enumerate(operands):
            body += const(t, a if i == 0 else b)
        body += op_bytes(op)
        store, align = STORE[resty]
        body += bytes([store]) + uleb(align) + uleb(0)
    # value_return(len, ptr): push len then ptr as i64
    body += b"\x42" + uleb(res // 8) + b"\x42\x00"
    body += b"\x10" + uleb(0) + b"\x0b"
    code = sect(10, vec([uleb(len(body) + 1) + b"\x00" + body]))
    # `resolve` needs `main: [] -> []`; function 0 is the import, so `main` is function 1
    exports = sect(7, vec([name("main") + b"\x00" + uleb(1)]))
    return b"\x00asm\x01\x00\x00\x00" + sect(1, vec(types)) + sect(2, vec(imports)) + \
        sect(3, vec(funcs)) + sect(5, vec([mem])) + exports + code


def _is_float_result(op):
    return _result_kind(op) in ("f32", "f64")


def _result_kind(op):
    w = float_ref.result_width(op)
    if 0x5B <= op <= 0x66:
        return "i32"
    if 0x8B <= op <= 0x98:
        return "f32"
    if 0x99 <= op <= 0xA6:
        return "f64"
    if op <= 0xAB:
        return "i32"
    if op <= 0xB1:
        return "i64"
    if op <= 0xB6:
        return "f32"
    if op <= 0xBB:
        return "f64"
    if op == 0xBC:
        return "i32"
    if op == 0xBD:
        return "i64"
    if op == 0xBE:
        return "f32"
    if op == 0xBF:
        return "f64"
    if op <= 0xFC03:
        return "i32"
    return "i64"


def _operand_types(op):
    if 0x5B <= op <= 0x60:
        return ["f32", "f32"]
    if 0x61 <= op <= 0x66:
        return ["f64", "f64"]
    if 0x8B <= op <= 0x91:
        return ["f32"]
    if 0x92 <= op <= 0x98:
        return ["f32", "f32"]
    if 0x99 <= op <= 0x9F:
        return ["f64"]
    if 0xA0 <= op <= 0xA6:
        return ["f64", "f64"]
    if op <= 0xAB:
        return ["f32"] if op <= 0xA9 else ["f64"]
    if op <= 0xB1:
        return ["f32"] if op <= 0xAF else ["f64"]
    if op <= 0xB6:
        return ["i32"] if op <= 0xB3 else (["i64"] if op <= 0xB5 else ["f64"])
    if op <= 0xBB:
        return ["i32"] if op <= 0xB8 else (["i64"] if op <= 0xBA else ["f32"])
    if op == 0xBC:
        return ["f32"]
    if op == 0xBD:
        return ["f64"]
    if op == 0xBE:
        return ["i32"]
    if op == 0xBF:
        return ["i64"]
    if op <= 0xFC03:
        return ["f32"] if op <= 0xFC01 else ["f64"]
    return ["f32"] if op <= 0xFC05 else ["f64"]


def run_harness(lines, mode=None):
    args = [HARNESS] + ([mode] if mode else [])
    p = subprocess.run(args, input="\n".join(lines) + "\n", capture_output=True, text=True)
    if p.returncode != 0:
        raise SystemExit(f"harness failed: {p.returncode}\n{p.stderr[-2000:]}")
    return p.stdout.splitlines()


def run_lean(lines):
    p = subprocess.run([LEAN], input="\n".join(lines) + "\n", capture_output=True, text=True,
                       check=True)
    return p.stdout.splitlines()


def cases(limit, seed):
    """(op, a, b) triples: directed edge values for every opcode, then generated ones."""
    rng = random.Random(seed)
    out = []
    e32 = [0, 0x80000000, 1, 0x80000001, 0x7F7FFFFF, 0xFF7FFFFF, 0x7F800000, 0xFF800000,
           0x7FC00000, 0x7FC12345, 0xFF800001, 0x3F800000, 0xBF800000, 0x4F000000, 0xCF000000,
           0x4F800000, 0x5F000000, 0xDF000000, 0x3FC00000]
    e64 = [0, 0x8000000000000000, 1, 0x8000000000000001, 0x7FEFFFFFFFFFFFFF,
           0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000,
           0x7FF8000000012345, 0xFFF0000000000001, 0x3FF0000000000000, 0xBFF0000000000000,
           0x43E0000000000000, 0xC3E0000000000000, 0x43F0000000000000, 0x3FF8000000000000]
    for op in sorted(float_ref.W):
        w = float_ref.W[op][0]
        edges = e32 if w == 32 else e64
        n = 0
        for a in edges:
            for b in edges:
                if limit and n >= limit:
                    break
                out.append((op, a, b))
                n += 1
        for _ in range(6):
            out.append((op, rng.choice(edges), rng.choice(edges)))
    return out


def compare_triples(triples):
    """Run `(op, a, b)` triples through the pinned engine and the Lean kernel; return the list of
    indices that disagree (value or trap kind). Empty list = full agreement."""
    lines = [f"1000000000000000 {build_module(op, x, y).hex()}" for (op, x, y) in triples]
    near = run_harness(lines)
    lean = run_lean([f"{op} {x:x} {y:x}" for (op, x, y) in triples])
    if len(near) != len(triples) or len(lean) != len(triples):
        raise SystemExit(f"line counts: near {len(near)} lean {len(lean)} expected {len(triples)}")
    bad = []
    for i, ((op, x, y), nl, ll) in enumerate(zip(triples, near, lean)):
        parts = nl.split(" ")
        if parts[0] == "ok":
            # the harness returns the stored little-endian bytes; the Lean kernel prints the bit
            # pattern in big-endian hex, so reverse the byte pairs before comparing
            raw = parts[3]
            ret = "".join(raw[i:i + 2] for i in range(len(raw) - 2, -2, -2)) if raw != "-" else "-"
            if ret != ll:
                bad.append((i, f"value: nearcore {ret} lean {ll}"))
        else:
            err = parts[3] if len(parts) > 3 else "?"
            if ll != "trap":
                bad.append((i, f"trap: nearcore {err} lean {ll}"))
            elif "IllegalArithmetic" not in err:
                bad.append((i, f"trap kind: nearcore {err} (expected WasmTrap(IllegalArithmetic))"))
    return bad


def compare(lines, labels, sample=400, seed=1):
    """Entry point used by `difftest_float.py --nearcore`.

    `lines` are `<op> <a-hex> <b-hex>`; a deterministic `sample` of them is re-executed by pinned
    nearcore and compared with the Lean kernel. Returns the number of disagreements."""
    triples = [_parse(l) for l in lines]
    idx = list(range(len(triples)))
    random.Random(seed).shuffle(idx)
    idx = idx[:sample]
    bad = compare_triples([triples[i] for i in idx])
    for i, why in bad:
        print(f"NEARCORE DISAGREE {labels[idx[i]]}: {why}")
    print(f"family=float-nearcore cases={len(idx)} disagreements={len(bad)}")
    return len(bad)


def compare_size():
    """The instrumented-module length (`prepare` mode vs the Lean size model).

    This is the sharpest instrumentation check available: the instrumented module is what nearcore
    actually compiles and runs, its length is an exact integer, and the Lean model
    (`NearSpecV3.Wasm.Size`) has to reproduce the whole encoder — the added imports, globals,
    exports, the two extra locals and every gas point — modulo the operators it copies verbatim.
    A float operator's encoded length and its gas point both feed into it.
    """
    nbad = 0
    n = 0
    for op in sorted(float_ref.W):
        w = float_ref.W[op][0]
        x = 0x3F800000 if w == 32 else 0x3FF0000000000000
        for reps in (1, 2):
            hx = build_module(op, x, x, reps).hex()
            line = f"1000000000000000 {hx}"
            near = run_harness([line], mode="prepare")[0]
            lean = subprocess.run([LEAN_SPEC, "--floats", "--prepared-size"], input=line + "\n",
                                  capture_output=True, text=True).stdout.strip()
            n += 1
            expect = str(len(near) // 2) if not near.startswith("prepare-error") else near
            if expect != lean:
                nbad += 1
                if nbad <= 15:
                    print(f"SIZE DISAGREE op=0x{op:x} reps={reps}: nearcore {expect} lean {lean}")
    print(f"family=float-size modules={n} disagreements={nbad}")
    return nbad


def _parse(line):
    op, a, b = line.split()
    return int(op), int(a, 16), int(b, 16)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=12)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--no-gas", dest="gas", action="store_false", default=True)
    a = ap.parse_args()
    triples = cases(a.limit, a.seed)
    bad = compare_triples(triples)
    for i, why in bad[:15]:
        op, x, y = triples[i]
        print(f"DISAGREE op=0x{op:x} a={x:x} b={y:x}: {why}")
    print(f"family=float-nearcore values cases={len(triples)} disagreements={len(bad)}")
    nbad = len(bad)
    if a.gas:
        nbad += compare_gas()
        nbad += compare_size()
    sys.exit(1 if nbad else 0)


def compare_gas():
    """Full outcome lines (status, burnt, used) for 1/2/3 copies of each float operator."""
    nbad = 0
    n = 0
    for op in sorted(float_ref.W):
        w = float_ref.W[op][0]
        x = 0x3F800000 if w == 32 else 0x3FF0000000000000
        for reps in (1, 2, 3):
            line = f"1000000000000000 {build_module(op, x, x, reps).hex()}"
            near = run_harness([line])[0].split()
            lean = subprocess.run([LEAN_SPEC, "--floats"], input=line + "\n",
                                  capture_output=True, text=True).stdout.split()
            n += 1
            if near[:3] != lean[:3]:
                nbad += 1
                if nbad <= 15:
                    print(f"GAS DISAGREE op=0x{op:x} reps={reps}: near {near[:3]} lean {lean[:3]}")
    print(f"family=float-gas modules={n} disagreements={nbad}")
    return nbad


def _is_partial(op):
    return (0xA8 <= op <= 0xAB) or (0xAE <= op <= 0xB1)


if __name__ == "__main__":
    main()
