# D3α checkpoint 2: Lean semantics of the integer WASM subset, and the difftest

Status: checkpoint 2 of `docs/requirements/D3_WASM_REQUIREMENTS.md` v0.2 §5, reported 2026-10-06, lane
`lane/v3-d3`. Evidence labels: **[P]** kernel-checked; **[T]** tested against pinned nearcore; **[src]**
read in source. Nothing in this checkpoint is proved beyond totality-by-construction.

## 1. What exists

**Specification**: `spec/lean/v3/NearSpecV3/Wasm/*.lean`, 2.6k LOC. These are new files only; the pinned
`spec/lean/v3/lakefile.toml` is unchanged.

| Module | Content |
|---|---|
| `Syntax` | D3α abstract syntax: flat operator arrays, every integer operator, refs, tables, bulk memory |
| `Decode` | binary decoder; wasmparser 0.228 implementation limits (names ≤ 100,000 B, br_table ≤ 131,072, ≤ 1,000 params) |
| `Validate` | WebAssembly 2.0 validation for NEAR's feature set (`C.refs`, data count, typed select, …) |
| `FiniteWasm` | literal ports of finite-wasm 0.6.1's max-stack simulation and gas analysis/optimiser |
| `InstrSize` | **exact** byte size of nearcore's instrumented module (decides `InstrumentedCodeTooLarge`) |
| `Prepare` | nearcore's `prepare_v3` as one interleaved pass, in nearcore's check order; finite-wasm limits; Wasmtime re-validation limits; link; method resolution |
| `HostSigs` | the 89 PV86 `env` signatures, generated from the checked inventory JSON |
| `Numerics` | width-generic i32/i64 integer semantics |
| `Exec` | small-step machine: NEAR gas counter with promise-lowered limits, Wasmtime call hooks, stack budget, paged memory, instantiation (globals, element/data segments, start), call/`call_indirect`, all D3α operators, and the host functions `value_return` (with data receivers), `panic`, `gas`, `promise_batch_create`, `promise_batch_action_function_call` |

Every definition is total: loops are bounded by input size, and execution by explicit fuel; fuel exhaustion
reports `unmodeled`. A grep finds no `sorry`/`axiom`/`native_decide`/`implemented_by`/`partial`/`unsafe` in
these files. `#print axioms` on `outcome` and `prepare` gives {propext, Classical.choice, Quot.sound}
**[P: axiom audit]**. Floats are **out of domain** (`InD3α`): the decoder parses them only so that it can report
`out-of-domain`.

**Oracle and difftest**: `oracle/wasm-d3/` (README there). The harness runs nearcore's production entry
points (`near_vm_runner::prepare` + `run`, PV86 config, Wasmtime/Winch), now with optional output data
receivers and the final balance. The Lean driver is `oracle/wasm-d3/lean`. Generators and `difftest.py`
are in `oracle/wasm-d3/tests`.

## 2. Results [T], all on the final build (pinned nearcore 2.13.4 `44f7ae6`, x86_64)

The comparison is the full outcome line: status, `burnt_gas`, `used_gas`, return bytes or the exact
`FunctionCallError`, and the balance on success. One text normalisation applies: wasmtime's message inside
`LinkError`/`WasmtimeCompileError` (the variant is still compared).

| Family | Cases | Compared | Out of domain | Disagreements |
|---|---|---|---|---|
| `opcodes` (per-opcode edges + structural + every preparation limit at limit/limit+1) | 9,167 | 9,166 | 1 | **0** |
| `random` seeds 1–4 (typed random D3α contracts) | 20,000 | 20,000 | 0 | **0** |
| `mutate` seeds 11–12 (byte-level mutants) | 20,000 | 19,717 | 283 | **0** |
| `promise` seeds 1–2 (promise + out-of-gas in a range, promise host errors, data receivers) | 10,000 | 10,000 | 0 | **0** |
| `sizes` (exact instrumented size vs nearcore's `prepare_contract` output) | 14,167 | 14,166 | 1 | **0** |
| **Total** | **73,334** | **73,049** | 285 | **0** |

Sensitivity check: the instrumentation ablation (`D3_LEAN_ARGS=--instruction-level-metering`) on `promise`
seed 1 gives **1,503 disagreements**, all in `burnt_gas`. That confirms review F1 on our own oracle: once a
promise exists, nearcore charges the whole finite-wasm range on out-of-gas, and the difftest catches a
per-instruction meter.

Outcome classes covered, by variant:
* **Preparation:** `TooManyTypes`, `TooManyFunctions`, `TooManyLocals`, `TooManyTables`,
  `TooManyTableElements`, `FunctionBodyTooLarge`, `TooManyParamsPerFunction`, `TooManyParamsPerContract`,
  `TooManyBlocksPerFunction`, `TooManyBlocksPerContract`, `OperandStackTooLarge`,
  `InstrumentedCodeTooLarge`, `Instantiate`, `Memory`, `Deserialization` (thousands of distinct causes via
  mutation).
* **Compile and link:** `WasmtimeCompileError`, `LinkError` (unknown import, mistyped import).
* **Method resolution:** `MethodNotFound`, `MethodInvalidSignature` (0-gas no-op outcome).
* **Traps:** `MemoryOutOfBounds` (memory, table, `call_indirect` index, instantiation segments),
  `IllegalArithmetic`, `Unreachable`, `IndirectCallToNull`, `IncorrectCallIndirectSignature`.
* **Host errors:** `GasExceeded`, `GasLimitExceeded`, `IntegerOverflow`, `MemoryAccessViolation` (stack budget
  and host out-of-bounds), `GuestPanic`, `InvalidRegisterId`, `ReturnedValueLengthExceeded`,
  `InvalidAccountId`, `BadUTF8`, `EmptyMethodName`, `InvalidPromiseIndex`, `BalanceExceeded`,
  `NumberPromisesExceeded`.

Throughput: nearcore about 2,000 cases/s; Lean about 50–80 cases/s on 8 cores for the random family, which is
dominated by 300 Tgas loops.

## 3. Findings of this checkpoint (all [T] against pinned nearcore, then [src])

1. **`externref` is rejected at PV86.** finite-wasm 0.6.1 passes `gc_types = false`
   (`features.rs:102`), and wasmparser 0.228 then admits only `funcref` (`validator.rs:286-290`). Found by
   the mutation family. Boundary doc B4 and requirements §2.1.1 have been corrected.
2. **A concrete H1 instance: Wasmtime re-validation rejects modules that NEAR's preparation accepts.**
   Instrumentation adds two locals per function, and Wasmtime 45 re-validates with wasmparser 0.248
   (`MAX_WASM_FUNCTION_LOCALS` = 50,000). A function with `params + locals ∈ {49,999, 50,000}` therefore
   passes `prepare` and then fails to compile: `CompilationError(WasmtimeCompileError)`, with 0 gas. This is
   modelled exactly, together with 0.248's 7,654,321-byte instrumented-body limit.
3. **finite-wasm's operand-stack analysis is a simulation, not the typed maximum.** `call_indirect` does not
   pop its index operand (`max_stack/instruction_visit.rs:362-364`). This is ported literally; it affects
   `OperandStackTooLarge` and the stack budget.
4. **`InstrumentedCodeTooLarge` is decided exactly.** The size model matches nearcore's prepared output
   byte-for-byte on 14,166 modules, including at the 16 MiB boundary. Contracts of any size are now in scope;
   the earlier conservative bound is gone.
5. **F1 is incorporated.** The gas model now has `promises_gas`, the promise-lowered `gas_limit`, and the
   `process_gas_limit` clamp to `min(prepaid, max_gas_burnt)`. The difftest exercises it (§2).

## 4. Review items (`docs/reviews/D3_REVIEW_2026-10-06.md`)

| Item | Status |
|---|---|
| F1 point table mandatory, `metering_equiv` retracted, promise family | done (docs, model, `promise` family, ablation caught) |
| F2 `LoadingError`/`WasmUnknownError` as 0-gas outcomes, H9 | done (boundary §2.2/§4, requirements table, H9) |
| F3 untested outcome rows | done except the empty-method row (the harness always calls `main`; the spec models it) |
| F4 (a)–(e) coverage | done (mutation; params/results; valued `br_table`; every limit at/over; data receivers) |
| F5 declarative range-charging invariant + clean-room metering | **open**: checkpoint 3 (C9 accepted into requirements) |
| F6 parser triple and 0.228 limits | done |
| F7 78 + 11 | done |
| F11 `compute_usage`, logs in the comparison | **open**: checkpoint 3 (harness and spec) |
| F12/F13 citations | F12 done; F13 noted |
| N3 `xs[i]!` in the spec | **open**: before the spec is pinned in a challenge, replace with proved-in-bounds or explicit failure |
| N4 exact shard line counts | done |
| N5 `--locked` | done (README) |

## 5. Not done, and what checkpoint 3 needs

* **Host functions:** 84 of 89 are unmodelled; calling one yields `unmodeled`, never a guessed outcome.
  Checkpoint 3 adds:
  * registers, context, economics, logs/panic_utf8/abort;
  * the remaining promises, yield/resume, storage with trie and recorded-storage coupling (H8);
  * validator, chain_id, the hashes;
  * `compute_usage` and logs in the comparison;
  * `RuntimeD3` integration and the oracle/v3 TestEnv traffic.
* **Independent implementation (requirements §2.2):** not started. Planned: the WASM core against
  WasmCert-Coq's extracted interpreter or the reference interpreter, and a clean-room metering
  reimplementation from a prose spec.
* **Proof obligations:** only totality-by-construction and the axiom audit so far. Open: decoder round trip
  where `Rel` uses it, and fuel never binding.
* **Scale:** 73k compared cases here. The requirements' 100,000-call target applies to the full-runtime
  difftest of checkpoint 3.
