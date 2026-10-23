#!/usr/bin/env python3
"""UQ-014 reproducer: the Wasmtime pooling-allocator `LoadingError` is REACHABLE at PV86.

`docs/research/near-wasm-boundary.md` §8 H9/H10 assume `LoadingError` never occurs on a correctly
provisioned node. That is false for a contract that *passes NEAR preparation* but whose compiled
instance exceeds the Wasmtime pooling allocator's 1 MiB `core_instance_size`
(`wasmtime-45.0.0/src/runtime/vm/instance/allocator/pooling.rs:179,422-441`), reached from
`near-vm-runner/src/wasmtime_runner/mod.rs:734-745`:

    Module::deserialize(..).map_err(|err| VMRunnerError::LoadingError(err.to_string()))?;

`Module::from_parts` validates the module against the allocator
(`wasmtime-45.0.0/src/runtime/module.rs:549-552`), so a module with enough defined globals fails
there. `function_call.rs:328-330` then turns that into a **0-gas** `nop_outcome` with
`FunctionCallError::LoadingError`, i.e. a consensus-observable *failed function call with zero burn*,
not a chunk rejection.

This script builds such a module from spec (not from any nearcore test fixture), then asserts:
  1. nearcore's own `prepare_contract` ACCEPTS it (so it is not a `PrepareError`), and
  2. running it through pinned nearcore yields `VMRunnerError::LoadingError`, and
  3. the Lean spec `nearspec-v3-wasm` returns `ok` for the same module — the divergence.

Exit 0 iff the divergence is reproduced exactly as described. A change in any leg (e.g. the Lean
spec learning the instance-size limit) makes this exit nonzero, by design: it is a regression test
for the *claim*, not a green-check.

Usage: uq014_instance_size.py [--harness PATH] [--lean PATH] [--globals N] [--keep DIR]
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_HARNESS = os.environ.get(
    "D3_HARNESS", "/data/illia/nearproof-deps/target-wasm-d3/release/near-wasm-d3-harness")
DEFAULT_LEAN = os.environ.get("D3_SPEC", os.path.join(HERE, "../lean/.lake/build/bin/nearspec-v3-wasm"))
# 65,505 globals run; 65,506 already fail. The instance-size requirement scales with
# num_defined_globals * sizeof(VMGlobalDefinition) + vmctx overhead, so the exact crossing is a
# wasmtime-layout detail; this script only asserts *some* N is reachable and both legs disagree.
GLOBALS = 66_000
PREPAID_GAS = 300_000_000_000_000


def build_module(n_globals, path):
    """A minimal module: memory export, `main`, then N immutable i32 globals.

    A `(memory (export "memory"))` is required by NEAR's prepared-module contract; the globals are
    what inflate Wasmtime's `Instance::alloc_layout` past `core_instance_size`."""
    with open(path, "w") as f:
        f.write('(module\n (memory (export "memory") 1)\n (func (export "main"))\n')
        for i in range(n_globals):
            f.write(f' (global (mut i32) (i32.const {i}))\n')
        f.write(')\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--harness", default=DEFAULT_HARNESS)
    ap.add_argument("--lean", default=DEFAULT_LEAN)
    ap.add_argument("--globals", type=int, default=GLOBALS)
    ap.add_argument("--keep", default=None, help="write the .wat/.wasm/.line here instead of a tmpdir")
    a = ap.parse_args()

    for p, what in ((a.harness, "nearcore harness"), (a.lean, "Lean wasm driver")):
        if not os.path.exists(p):
            sys.exit(f"SKIP: {what} not built: {p}")

    tmp = a.keep or tempfile.mkdtemp(prefix="uq014-")
    os.makedirs(tmp, exist_ok=True)
    wat = os.path.join(tmp, "globals.wat")
    wasm = os.path.join(tmp, "globals.wasm")
    line = os.path.join(tmp, "case.line")
    build_module(a.globals, wat)
    if shutil.which("wasm-tools"):
        subprocess.run(["wasm-tools", "parse", wat, "-o", wasm], check=True)
    elif shutil.which("wat2wasm"):
        subprocess.run(["wat2wasm", wat, "-o", wasm], check=True)
    else:
        sys.exit("SKIP: need wasm-tools or wat2wasm to assemble the .wat")
    code = open(wasm, "rb").read()
    with open(line, "w") as f:
        f.write(f"{PREPAID_GAS} {code.hex()}\n")

    fails = []

    # Leg 1: nearcore preparation accepts it (not a PrepareError / CompilationError).
    with open(line, "rb") as f:
        prep = subprocess.run([a.harness, "prepare"], stdin=f, capture_output=True, text=True)
    prep_out = prep.stdout.strip()
    ok_prep = bool(prep_out) and not prep_out.startswith("prepare-error")
    print(f"[1] nearcore prepare: {'accepted' if ok_prep else 'REJECTED'}"
          f" ({len(prep_out) // 2} instrumented bytes)")
    if not ok_prep:
        fails.append("nearcore preparation rejected the module, so this is not a LoadingError case")

    # Leg 2: running it yields VMRunnerError::LoadingError -> the harness cannot print an outcome.
    with open(line, "rb") as f:
        run = subprocess.run([a.harness], stdin=f, capture_output=True, text=True)
    combined = run.stdout + run.stderr
    hit = "LoadingError" in combined
    print(f"[2] nearcore run: {'LoadingError (panic in harness)' if hit else 'no LoadingError'}")
    if not hit:
        fails.append(f"nearcore did not report LoadingError; got: {combined.strip()[:300]}")

    # The specific allocator message proves the *pooling instance size* branch, not a stale cache.
    size_msg = "does not fit in pooling allocator requirements" in combined
    print(f"[2b] message is the pooling-allocator instance-size branch: {size_msg}")
    if not size_msg:
        fails.append("LoadingError came from a different branch (not core_instance_size)")

    # Leg 3: the Lean spec accepts the same module -> divergence.
    with open(line, "rb") as f:
        lean = subprocess.run([a.lean], stdin=f, capture_output=True, text=True)
    lean_out = lean.stdout.strip()
    lean_ok = lean_out.startswith("ok ")
    print(f"[3] Lean nearspec-v3-wasm: {lean_out[:120]}")
    if not lean_ok:
        fails.append("the Lean spec did not return `ok`, so there is no divergence to report")

    print()
    if fails:
        print("UQ-014 CLAIM NOT REPRODUCED:")
        for x in fails:
            print(f"  - {x}")
        return 1
    print("UQ-014 CONFIRMED: `LoadingError` (pooling-allocator instance size) is reachable at PV86 for a")
    print("contract that passes preparation; nearcore burns 0 gas and reports a failed function call,")
    print("while the Lean spec (`checkD3` via `prepare`/`instantiate`) accepts it.")
    print(f"artifacts: {tmp}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
