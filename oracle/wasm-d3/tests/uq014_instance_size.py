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

This regression builds a module independently, checks preparation succeeds, then compares
nearcore's runtime outcome with the successor Lean runtime. The removed-check control must
reproduce the historical success/failure divergence. Exit zero requires parity AND that control.

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
DEFAULT_LEAN = os.environ.get("D3_SPEC", os.path.join(HERE, "../../../spec/lean/v3/.lake/build/bin/nearspec-v3-runtime"))
# 65,505 globals run; 65,506 already fail. The instance-size requirement scales with
# num_defined_globals * sizeof(VMGlobalDefinition) + vmctx overhead, so the exact crossing is a
# wasmtime-layout detail; this script checks a reachable failure and detects removal of its semantics.
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
        prep = subprocess.run([a.harness, "prepare"], stdin=f, capture_output=True, text=True, timeout=120)
    prep_out = prep.stdout.strip()
    ok_prep = prep.returncode == 0 and bool(prep_out) and all(c in "0123456789abcdefABCDEF" for c in prep_out)
    print(f"[1] nearcore prepare: {'accepted' if ok_prep else 'REJECTED'}"
          f" ({len(prep_out) // 2} instrumented bytes)")
    if not ok_prep:
        fails.append("nearcore preparation rejected the module, so this is not a LoadingError case")

    # Runtime conversion is the pinned function_call.rs LoadingError -> nop_outcome.
    with open(line, "rb") as f:
        run = subprocess.run([a.harness, "runtime-full"], stdin=f,
                             capture_output=True, text=True, timeout=120)
    oracle_out = run.stdout.strip()
    if run.returncode or "LoadingError" not in oracle_out or "does not fit in pooling allocator requirements" not in oracle_out:
        fails.append(f"nearcore did not report pooling LoadingError: {oracle_out[:300]}")
    lean = subprocess.run([a.lean, wasm], capture_output=True, text=True, timeout=120)
    lean_out = lean.stdout.strip()
    print(f"[2] nearcore: {oracle_out[:180]}")
    print(f"[3] Lean: {lean_out[:180]}")
    if lean.returncode or lean_out != oracle_out:
        fails.append("successor full runtime outcome differs from nearcore")
    ablation = subprocess.run([a.lean, wasm, "main", "--ablate-loading-limits"],
                             capture_output=True, text=True, timeout=120)
    if ablation.returncode or not ablation.stdout.startswith("ok "):
        fails.append("removed-check control did not reproduce the historical divergence")

    print()
    if fails:
        print("UQ-014 REGRESSION FAILED:")
        for x in fails:
            print(f"  - {x}")
        return 1
    print("UQ-014 PARITY PASSED: full zero-gas LoadingError outcome; removed-check control detected")
    print(f"artifacts: {tmp}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
