# D3 checkpoint-1 PoC: a Lean executable semantics for a NEAR WASM subset, differential-tested against nearcore

This is research. It is not part of any trusted tree. It deliberately lives outside `spec/lean` so that it
changes no `TreeDigest`.

The PoC checks one claim: the NEAR-specific parts of contract execution can be stated as an executable Lean
definition **over the original module bytes** and still agree with pinned nearcore to the last unit of gas.
Those parts are preparation, finite-wasm gas instrumentation, the stack budget, Wasmtime's gas hooks, host
gas and the outcome mapping. See `docs/research/near-wasm-boundary.md` and `docs/research/near-wasm-strategy.md`.

## Components

| Path | What |
|---|---|
| `lean/` (Lake package `WasmPoC`, Lean 4.34.1, no dependencies) | `Decode` (binary format), `Prepare` (validation with finite-wasm's max-operand-stack, a port of the finite-wasm 0.6.1 gas analysis and optimiser, block matching, NEAR prologue constants), `Exec` (small-step machine, NEAR gas counter and Wasmtime hooks, `value_return`/`panic`, outcome line). Every definition is total: loops are bounded by input size and execution by explicit fuel. No `sorry`/`axiom`/`native_decide`/`implemented_by`. The only `partial` is the stdin driver in `Main.lean`. |
| `../../oracle/wasm-d3/` | Rust harness linked against pinned nearcore 2.13.4 `near-vm-runner` (`oracle/vendor/nearcore`, `oracle/scripts/link-nearcore.sh`). It runs `near_vm_runner::prepare` + `run` with `RuntimeConfigStore::new(None).get_config(86)` and asserts `vm_kind == Wasmtime`; the context has no output-data receivers. |
| `gen_wasm.py` | Typed random module generator; see families below. |
| `difftest.py` | Runs both implementations on identical bytes and compares full outcome lines. |

**Subset.** Imports `env.value_return(i64,i64)` and `env.panic()`; one memory; i32 values (i64 only as
host-call arguments); `i32.const`, `local.get/set/tee`, `drop`, `nop`, `select`, all i32 unop/binop/relop/eqz,
`i32.load`, `i32.load8_u`, `i32.store`, `i32.store8` (any offset), `memory.size`, `memory.grow`,
`block`/`loop`/`if`/`else` (empty or i32 result), `br`, `br_if`, `br_table`, `return`, `unreachable`, and
`call`, with recursion between up to three functions. Excluded: floats, i64 arithmetic, tables,
`call_indirect`, globals, bulk memory, data segments, and the other 87 host functions.

**Outcome line** (identical format on both sides): `ok <burnt> <used> <return-hex|->` or
`abort <burnt> <used> <FunctionCallError Debug>`.

**Generator families**
* `random`: nested typed code, traps (div/rem by 0 and INT_MIN/−1, out-of-bounds at the 64 MiB edge and at
  32-bit offsets, `unreachable`), `memory.grow` within and beyond 2,048 pages, host errors
  (`InvalidRegisterId` via `len = u64::MAX`, `MemoryAccessViolation`, `ReturnedValueLengthExceeded`,
  `IntegerOverflow` from `read_memory_byte × len`, `GasLimitExceeded` from huge `len`), `GuestPanic`,
  prepaid gas from below the loading fee up to 300 Tgas, unbounded loops. About 1 in 15 modules declares no
  memory while using memory ops; nearcore rejects these during preparation with 0 gas.
* `window`: `memory.grow(~1.2·10^9)` burns about 10^15 gas, followed by one long pure straight-line run, with
  `prepaid = 10^15 − δ`. This lands out-of-gas inside a finite-wasm basic block, where block-level and
  instruction-level metering report different error variants.
* `recursion`: unbounded self-recursion that ends in stack-budget exhaustion
  (`HostError(MemoryAccessViolation)`) or out of gas. This exercises the operand-stack + frame accounting.

## Reproduce

```sh
# once: link pinned nearcore and build the harness (no sccache for nearcore)
oracle/scripts/link-nearcore.sh
cd oracle/wasm-d3 && RUSTC_WRAPPER= CARGO_TARGET_DIR=/data/illia/nearproof-deps/target-wasm-d3 \
  taskset -c 8-15,24-31 /data/illia/nearproof-deps/bin/heavy cargo build --release -j 16
# Lean
cd examples/d3-wasm-poc/lean && taskset -c 8-15,24-31 lake build
# difftest: N cases, seed, Lean shards
cd examples/d3-wasm-poc && taskset -c 8-15,24-31 python3 difftest.py 2000 1
```

## Results

See `RESULTS.md` (the run log, appended per run).
