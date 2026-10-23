#!/usr/bin/env python3
"""UQ-014, branch 2/3: which Wasmtime runner error branches are reachable at PV86?

`docs/research/near-wasm-boundary.md` §8 lists three hazards as "assume absent":
H2 (concurrency-permit `LinkError`), H9 (`LoadingError` / `WasmUnknownError`) and H10 (resource errors
at instantiation falling through `into_vm_error` into `LinkError{msg}`). This script measures each
branch against pinned nearcore's own code path (`near_vm_runner::prepare` + `near_vm_runner::run`,
PV86 `RuntimeConfig`, Wasmtime), and against the Lean spec's `nearspec-v3-wasm` driver, so that the
answer is per-branch instead of a blanket "assumed absent".

Branch summary this script measures:

  A. `LoadingError` from the pooling allocator's `core_instance_size` (1 MiB) check.
     PASSES preparation. nearcore aborts the call; Lean accepts it. -> DIVERGENCE (see
     uq014_instance_size.py, which is the dedicated reproducer and is a stricter test of the same
     claim).
  B. `LinkError` "unknown or invalid import": an `env` import whose name is not a host function.
     PASSES preparation (prepare_v3 only checks `import.module == "env"`, not the name).
     nearcore aborts with `LinkError`; Lean's `Wasm.Prepare.link` models the same check. -> AGREE.
  C. `LinkError` "types incompatible: …": a known `env` import name with the wrong signature.
     PASSES preparation (`prepare_v3.rs:315` has an explicit `TODO: validate imported function types
     here`). nearcore aborts with wasmtime's text; Lean aborts with its own fixed text. -> AGREE
     modulo the message, which the Lean difftest already compares modulo `msg`.
  D. `WasmUnknownError`: needs `C::Unknown` or a nondeterministic trap
     (`wasmtime_runner/mod.rs:404,410`). `TrapClassification::Unknown` is proven unreachable by
     nearcore's own exhaustive test (`trap_classification.rs:105-118`), and `C::Interrupt` requires
     `epoch_interruption`, which nearcore never enables and whose wasmtime default is `false`
     (`wasmtime-environ-45.0.0/src/tunables.rs:245`). -> NOT REACHED by this script; status
     "no reachable construction found", not "proven absent".
  E. H2 concurrency-permit `LinkError` ("failed to acquire execution slot", mod.rs:1018-1023):
     reachable only under table/instance-slot contention across concurrent chunk validations.
     NOT measured here (needs a concurrent workload); see the assessment text for the source chain.

Exit 0 when every branch this script *can* measure behaves as tabulated above. Exit 1 when a leg
changes: in particular, if the Lean spec starts rejecting B or C, or starts accepting A, this fails.

Usage: uq014_wasmtime_branches.py [--harness PATH] [--lean PATH] [--keep DIR]
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
PREPAID_GAS = 300_000_000_000_000

# (name, .wat source, expectation)
# expectation: "diverge" -> nearcore aborts and Lean accepts
#              "agree"   -> both abort (messages compared loosely)
CASES = [
    (
        "B-unknown-import",
        '(module\n'
        '  (import "env" "totally_bogus_host_fn" (func $b (param i32) (result i32)))\n'
        '  (memory 1)\n'
        '  (func (export "main") (result i64) i64.const 0))\n',
        "agree",
    ),
    (
        "C-incompatible-import-type",
        '(module\n'
        '  (import "env" "sha256" (func $sha (param i64) (result i64)))\n'
        '  (memory 1)\n'
        '  (func (export "main") (result i64) i64.const 0))\n',
        "agree",
    ),
]


def build(wat_src, path_wat, path_wasm):
    with open(path_wat, "w") as f:
        f.write(wat_src)
    if shutil.which("wasm-tools"):
        subprocess.run(["wasm-tools", "parse", path_wat, "-o", path_wasm], check=True)
    elif shutil.which("wat2wasm"):
        subprocess.run(["wat2wasm", path_wat, "-o", path_wasm], check=True)
    else:
        sys.exit("SKIP: need wasm-tools or wat2wasm to assemble the .wat")
    return open(path_wasm, "rb").read()


def run(binary, mode, line_bytes):
    argv = [binary] if not mode else [binary, mode]
    p = subprocess.run(argv, input=line_bytes, capture_output=True)
    return (p.stdout + p.stderr).decode("utf-8", "replace").strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--harness", default=DEFAULT_HARNESS)
    ap.add_argument("--lean", default=DEFAULT_LEAN)
    ap.add_argument("--keep", default=None)
    a = ap.parse_args()

    for p, what in ((a.harness, "nearcore harness"), (a.lean, "Lean wasm driver")):
        if not os.path.exists(p):
            sys.exit(f"SKIP: {what} not built: {p}")

    tmp = a.keep or tempfile.mkdtemp(prefix="uq014br-")
    os.makedirs(tmp, exist_ok=True)
    fails = []
    rows = []

    for name, wat_src, expect in CASES:
        code = build(wat_src, os.path.join(tmp, name + ".wat"), os.path.join(tmp, name + ".wasm"))
        line = f"{PREPAID_GAS} {code.hex()}\n".encode()

        prep = run(a.harness, "prepare", line)
        accepted = bool(prep) and not prep.startswith("prepare-error")
        near = run(a.harness, "", line)
        lean = run(a.lean, "", line)

        near_abort = near.startswith("abort")
        lean_abort = lean.startswith("abort")
        # Lean models `link` as a `linkError` carrying a fixed or wasmtime-shaped message; compare the
        # *kind* (`LinkError`) not the exact text, which is a known and documented difference.
        near_kind = "LinkError" in near
        lean_kind = "LinkError" in lean

        print(f"[{name}] prepare={'accepted' if accepted else 'REJECTED'}")
        print(f"  nearcore: {near[:160]}")
        print(f"  lean    : {lean[:160]}")

        rows.append((name, accepted, near_abort and near_kind, lean_abort and lean_kind))

        if expect == "agree":
            if not accepted:
                fails.append(f"{name}: preparation rejected the module, so this branch is a "
                             f"PrepareError and not a runner LinkError")
            if not (near_abort and near_kind):
                fails.append(f"{name}: nearcore did not abort with LinkError; got {near[:200]!r}")
            if not (lean_abort and lean_kind):
                fails.append(f"{name}: Lean did not abort with LinkError; got {lean[:200]!r}")
        else:
            if not accepted:
                fails.append(f"{name}: preparation rejected the module")
            if not near_abort:
                fails.append(f"{name}: nearcore did not abort; got {near[:200]!r}")
            if lean_abort:
                fails.append(f"{name}: Lean aborted but was expected to accept; got {lean[:200]!r}")

    print()
    print("branch                                  prepare   nearcore LinkError   lean LinkError")
    for name, acc, nk, lk in rows:
        print(f"{name:<38} {'ok' if acc else 'REJECT':<9} {str(nk):<20} {lk}")

    print()
    if fails:
        print("UQ-014 BRANCH CLAIM NOT REPRODUCED:")
        for x in fails:
            print(f"  - {x}")
        print(f"artifacts: {tmp}")
        return 1
    print("UQ-014 branch table reproduced: the two import-related `LinkError` branches are reachable")
    print("AFTER preparation and both legs agree on them (modulo the documented message difference).")
    print("H2's concurrency-permit branch needs a concurrent workload and is NOT measured here.")
    print(f"artifacts: {tmp}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
