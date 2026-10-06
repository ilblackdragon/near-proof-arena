# The NEAR WASM boundary at PV86 (nearcore 2.13.4): what a `FunctionCall` executes

Status: research, D3 checkpoint 1 (`docs/requirements/D3_WASM_REQUIREMENTS.md` §5.1).
Lane `lane/v3-d3`, 2026-10-06.

Pinned source: nearcore **2.13.4** (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, `oracle/NEARCORE_PIN`),
protocol version **86**, mainnet parameters. Unless prefixed, paths are relative to
`runtime/near-vm-runner/src/` in that checkout. `W:` is short for `wasmtime_runner/`.
Third-party crates are cited at the versions locked by nearcore's `Cargo.lock`: wasmtime/winch-codegen
45.0.0, finite-wasm 0.6.1, wasmparser 0.236.

Companion documents:
* `docs/research/near-wasm-strategy.md`: formal-semantics and proving strategy, effort, recommendation (deliverable 2).
* `docs/research/wasm-formal-survey.md`: survey of existing formal WASM semantics and zk-WASM systems.
* `examples/d3-wasm-poc/`: Lean executable semantics for a small subset, plus the nearcore differential harness (deliverable 3, §10).

**Evidence labels.** In this document, **[src]** means read in the pinned source with a citation. **[tested]**
means observed by running the pinned `near-vm-runner` through `oracle/wasm-d3`. Nothing here is proved.

---

## 0. Summary (the facts that shape D3)

| # | Fact | Evidence |
|---|---|---|
| B1 | At PV86 the VM is **Wasmtime 45**, and NearVM is no longer used. `vm_kind` switched NearVm→Wasmtime at PV84 (`core/parameters/res/runtime_configs/84.yaml:2`). There is no `86.yaml`, so PV86 uses the PV85 config (snapshot `core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`). | [src] |
| B2 | The code generator is **Winch** (a single-pass baseline compiler) on x86_64 and **Cranelift** on every other arch (`W:mod.rs:512-521`). Consensus therefore assumes Winch-x86_64 and Cranelift-aarch64 agree bit for bit. | [src] |
| B3 | **Floats are allowed**, and NaNs are **canonicalised** (`cranelift_nan_canonicalization(true)`, `W:mod.rs:531-534`, honoured by Winch at codegen: `winch-codegen-45.0.0/src/isa/x64/masm.rs:716-737`). The canonical NaN is the positive quiet NaN `0x7FC00000` / `0x7FF8000000000000` (`winch-codegen/src/masm.rs:16-17`). It is applied after 24 ops: f32/f64 add, sub, mul, div, min, max, sqrt, ceil, floor, trunc, nearest, and promote/demote. `abs`, `neg`, `copysign`, loads and reinterprets are bitwise and are not canonicalised. | [src] |
| B4 | Feature set accepted from **contracts** (`features.rs:71-109`, validated by wasmparser through finite-wasm 0.6): MVP + floats + mutable globals + **sign-extension** + **saturating float→int** + **reference types + bulk memory** (`reftypes_bulk_memory = true` from PV84). Everything else is rejected: multi-value, SIMD, relaxed SIMD, threads, tail calls, multi-memory, memory64, exceptions, extended-const, GC, function references, memory control, custom page sizes, stack switching and wide arithmetic. | [src] |
| B5 | The **prepared** module itself uses one proposal that contracts may not use: the instrumentation emits **wide-arithmetic** ops (`i64.add128`, `i64.sub128`, `i64.mul_wide_u`) for overflow checks (`prepare/instrument_v3.rs:178-231`), and Wasmtime is configured with `wasm_wide_arithmetic(true)` (`W:mod.rs:545`). A spec stated literally over prepared bytes must therefore include that proposal. The PoC instead specifies the instrumentation's *meaning* (§4) and avoids it. | [src] |
| B6 | Gas is metered by **finite-wasm instrumentation**, not by Wasmtime fuel. A `remaining_gas: i64` global is checked and decremented at **per-basic-block** instrumentation points, and Wasmtime call hooks synchronise it with the host `GasCounter` (`W:mod.rs:1042-1072`). | [src], [tested] |
| B7 | Stack depth is limited by instrumentation, not by Wasmtime. Every function entry charges `max_operand_stack_bytes + frame_bytes` against a 262,144-"byte" budget, and exhaustion is reported as **`HostError::MemoryAccessViolation`**, not as a trap (`W:logic.rs:290-292`). | [src], [tested] |
| B8 | Memory is **normalised**: whatever the contract declares, the prepared module has `(memory 1024 2048)`, so it starts at 64 MiB and is capped at 128 MiB (`prepare/prepare_v3.rs:126-139,371-379`). The contract must still *declare* a memory if it uses memory instructions, because validation runs on the original module. | [src], [tested] |
| B9 | At PV86 there are **89 importable host functions** (module `env`): 76 always-on, plus 13 behind PV85 flags that are all on. Table: Appendix A. | [src] |
| B10 | Only the **failure bit** of an execution status reaches the outcome root (`PartialExecutionStatus`, `core/primitives/src/transaction.rs:597-613`). The error kind (`GasExceeded` vs `GasLimitExceeded`, trap class, …) is not consensus-observable. Gas, logs, return value, receipts and state changes are. | [src] |
| B11 | `fix_contract_loading_cost = false` at PV86. A contract that fails preparation or compilation burns **0 gas**, a missing method or bad signature gives a **zero-gas no-op outcome**, and a link error burns the contract-loading fee (§2.3). | [src], [tested] |

---

## 1. Where a `FunctionCall` enters the VM

`runtime/runtime/src/actions.rs` (`action_function_call`) → `runtime/runtime/src/function_call.rs`
→ `near_vm_runner::prepare(contract, wasm_config, cache, gas_counter, method)` (`runner.rs:54-66`) →
`near_vm_runner::run(prepared, ext, context, fees)` (`runner.rs:89-109`). The VM is chosen by
`config.vm_kind.runtime(config)` (`runner.rs:204-227`). `VMKind::Wasmtime` builds `WasmtimeVM`
(`runner.rs:216-217`). `node-runtime` compiles near-vm-runner with both `near_vm` and `wasmtime_vm`
(`runtime/runtime/Cargo.toml:37`), and the protocol config picks Wasmtime.

The `GasCounter` comes from `VMContext::make_gas_counter` (`logic/context.rs:75-87`):
`prepaid_gas` from the receipt and `max_gas_burnt = 10^15` (PV83 raised it, `83.yaml`). The fast limit is
`min(max_gas_burnt, prepaid_gas)` (`logic/gas_counter.rs:85-108`).

## 2. Compile, cache, instantiate: the parts that are semantics

### 2.1 Pipeline (`W:mod.rs:683-817, 874-923, 982-1094`)

1. **Cache key** = `get_contract_cache_key(code_hash, config, vm_hash)` (`W:mod.rs:699`). `vm_hash` folds
   in Wasmtime's `precompile_compatibility_hash` and a local version `73` (`W:mod.rs:555-564`).
2. On a miss: `compile_uncached` = `prepare::prepare_contract(code, config, Wasmtime)` (§3), then
   `engine.precompile_module` (`W:mod.rs:567-594`). **Both failure kinds are cached as results**
   (`CompiledContract::CompileModuleError`, `W:mod.rs:666-673`).
3. `Module::deserialize` and a lookup of the `memory`, `remaining_gas` and `start` exports. The linker gets every
   `env` import enabled by the config, and `instantiate_pre` runs (`W:mod.rs:744-784`).
4. Gas: `before_loading_executable` rejects an empty method name. `after_loading_executable` charges
   `contract_loading_bytes × |wasm| + contract_loading_base`, but **only on a successful load**, because
   `fix_contract_loading_cost = false` (`logic/gas_counter.rs:235-270`, `W:mod.rs:797-816`).
5. Method resolution: the export `"\0" ++ method` must exist and have type `[] → []`
   (`W:mod.rs:887-902`; the prefix is `EXPORT_PREFIX = "\0"`, `lib.rs:50`).
6. `run`: a new `Store`, `StoreLimits` (1 instance, 1 memory ≤ 2048 pages, tables ≤ `max_tables_per_contract`,
   elements ≤ 10,000) (`W:mod.rs:314-362`), a concurrency permit, `instantiate`, then the gas global
   hooks, the `start` export (the contract's start function, which the instrumentation re-exported so it runs
   *after* gas is set up, `instrument_v3.rs:318-328`), and finally the method (`W:mod.rs:982-1094`).

### 2.2 What of caching is semantically relevant

The cache is semantically transparent, **except** that its stored values are consensus-relevant outcomes:
* *Prepare result*: any `PrepareError` → `CompilationError(PrepareError(e))` with 0 gas.
* *Wasmtime/Winch compile result*: `CompilationError(WasmtimeCompileError{msg})` with 0 gas
  (`W:mod.rs:571-580`). **Hazard H1.** The outcome depends on whether *Winch* (x86_64) or *Cranelift*
  (aarch64) accepts a prepared module. The guard `max_instrumented_code_size = 16 MiB` exists because of
  Cranelift's 24-bit SSA value limit (`prepare_v3.rs:458-468`). The spec has to model "the compiler accepts
  every prepared module within the limits" as an assumption, tested but unprovable.
* *Link result*: an unknown import or a signature mismatch gives `LinkError{msg}`, cached in the memory cache.
  It is charged the loading fee (`W:mod.rs:757-764, 915-918`).

A corrupted or stale on-disk cache is outside the semantics (`VMRunnerError::LoadingError`, i.e. node failure).
One more path is not modelled: **H2**, the concurrency semaphore. `try_acquire` returns `None` only after
2^16 contended iterations, which yields `LinkError("failed to acquire execution slot")` (`W:mod.rs:1012-1018`).
That is non-deterministic in principle, unreachable in practice, and must be stated as an assumption.

### 2.3 Preparation and link outcomes (gas at PV86)

| Situation | `VMOutcome` | burnt gas | Source |
|---|---|---|---|
| `PrepareError::*` / Winch compile error | `abort(CompilationError(..))` | 0 | `W:mod.rs:811-815` |
| empty method name | `abort(MethodResolveError(MethodEmptyName))` | 0 | `gas_counter.rs:241-246` |
| loading fee exceeds gas | `abort(HostError(GasExceeded))` (always this variant) | clamped to `min(prepaid, max_burnt)` | `gas_counter.rs:259-270` |
| method missing / signature ≠ `[]→[]` | `nop_outcome(MethodResolveError(..))` | **0** (loading fee discarded) | `W:mod.rs:887-902`, `logic/logic.rs:4511-4540` |
| unknown/mistyped import | `abort(LinkError{msg})` | loading fee | `W:mod.rs:757-764, 414-419` |
| instantiation trap (data/elem segment out of bounds) | `abort(WasmTrap(MemoryOutOfBounds))` | loading fee | `W:mod.rs:1019-1026`, `385-394` |

**[tested]**: the 0-gas `PrepareError(Deserialization)` row (examples/d3-wasm-poc, §10).

## 3. Preparation (`prepare.rs:22-33` → `prepare/prepare_v3.rs`)

`prepare_v3` is used whenever `reftypes_bulk_memory || vm_kind == Wasmtime` (`prepare.rs:28-29`).

### 3.1 Early pass: validation and normalisation (`prepare_v3.rs:61-301`)
A single wasmparser pass over the *original* module, with `Validator::new_with_features(NEAR features)`:
* any parse or validation failure → `PrepareError::Deserialization`;
* **imports**: module must be `"env"` (else `Instantiate`); table/global imports → `Instantiate`;
  memory import → `Memory`; tag → `Deserialization`. Function import names and types are *not*
  checked here; they surface as `LinkError` at link time (`prepare_v3.rs:303-333`);
* **memory**: any declared memory is replaced by `(memory 1024 2048)` and the memory export is
  removed. `memory` is always exported, and a memory section is synthesised when absent
  (`prepare_v3.rs:126-139,175,192-194,347-379`);
* **exports**: every non-memory export is renamed to `"\0" ++ name` (`prepare_v3.rs:147-196`), so
  exports are unreachable by `method_name` unless they are functions of type `[]→[]`;
* **custom sections are discarded** (`discard_custom_sections = true`, `prepare_v3.rs:272-277`);
* any other section (tags, component model, unknown) → `Deserialization` (`prepare_v3.rs:279-296`).

### 3.2 Limits enforced at PV86 (values from the PV85 snapshot)

| Limit | Value | Error | Where |
|---|---|---|---|
| `max_types_per_contract` | 1,024 | `TooManyTypes` | `prepare_v3.rs:81-90` |
| `max_functions_number_per_contract` (imports + defined) | 10,000 | `TooManyFunctions` | `:225-235, 316-317` |
| `max_tables_per_contract` | 1 | `TooManyTables` | `:107-125` |
| `max_elements_per_contract_table` (initial size) | 10,000 | `TooManyTableElements` | `:120-122` |
| `max_function_body_size` | 196,608 B | `FunctionBodyTooLarge` | `:236-246` |
| `max_locals_per_contract` | 1,000,000 | `TooManyLocals` | `:247-255` |
| `max_params_per_function` / `_per_contract` | 64 / 50,000 | `TooManyParams*` | `instrument_v3.rs:492-501` |
| `max_blocks_per_function` / `_per_contract` | 5,000 / 50,000 | `TooManyBlocks*` | `instrument_v3.rs:594-606,684-687` |
| `max_operand_stack_bytes_per_function` | 8,192 | `OperandStackTooLarge` | `instrument_v3.rs:526-529` |
| `max_instrumented_code_size` | 16 MiB | `InstrumentedCodeTooLarge` | `prepare_v3.rs:463-468` |
| `max_contract_size` (deploy-time, not prepare) | 4 MiB | action error | runtime |
| memory: initial / max pages | 1,024 / 2,048 | (normalised) | snapshot `limit_config` |
| `max_stack_height` | 262,144 | runtime `MemoryAccessViolation` | `instrument_v3.rs:576-585` |

Any other finite-wasm analysis failure → `Deserialization`. Any other instrumentation failure → `Serialization`
(`prepare_v3.rs:426-457`).

### 3.3 Instrumentation (`prepare/instrument_v3.rs`, adapted from finite-wasm)

Three functions are imported from module `internal` and prepended, which shifts every function index by 3:
`finite_wasm_gas_exhausted`, `finite_wasm_stack_exhausted`, `finite_wasm_gas(i64)` (`:694-725`).
Two i64 globals are added: `GAS` (exported as `remaining_gas`) and `STACK` (initialised to 262,144)
(`:727-745`). Every function body is wrapped in a `block` and gets:

1. **Prologue** (`:560-593`): `STACK := STACK − (op_stack_max + frame)` computed as a 128-bit subtraction;
   a borrow calls `stack_exhausted`. Then a gas point of constant `⌈frame/8⌉ · regular_op_cost`. Here `frame =
   64 + Σ size(param/local)` with sizes i32/f32 = 4, i64/f64 = 8, v128 = 16, ref = 8 (`prepare_v3.rs:473-505`).
   `op_stack_max` is finite-wasm's static maximum of the operand stack in bytes (`finite-wasm/src/max_stack`).
2. **Gas points** at the offsets chosen by finite-wasm's analysis (`:609-620`, `:800-880`):
   `if GAS < c then finite_wasm_gas(c); unreachable else GAS -= c`. For the bulk/grow ops the charge is
   `count·linear + constant`, using 128-bit overflow checks that call `gas_exhausted` on overflow.
3. **Epilogue**: `STACK += charge` before every `return`/`return_call*` and after the wrapping block
   (`:634-671`, `:788-798`).

**The gas analysis** (finite-wasm 0.6.1 `src/gas/mod.rs`, `src/gas/optimize.rs`) assigns every operator a
fee from `SimpleGasCostCfg` (`prepare_v3.rs:507-546`): `block`/`end`/`else` = 0; `memory.grow`,
`memory.{init,copy,fill}` and `table.{grow,init,copy,fill}` = `linear_op_base_cost + linear_op_unit_cost ×
count` (26,328,192 + 822,756·n); **every other operator = `regular_op_cost` = 822,756**. Points are then
merged: same-offset points first, then runs of *pure* instructions are merged forward into the next
control-flow point. A gas point therefore covers a straight-line range that ends at the first potentially
trapping, branching or side-effecting instruction. The cost of `loop` is charged at the loop *body* start,
so it is paid on every iteration.

Observable consequences (all **[tested]** by the PoC):
* **Out-of-gas is detected one basic block early.** For the *amount* of gas this is unobservable, because both
  models clamp `burnt` to `min(prepaid, max_gas_burnt)`. It is observable for the **error variant**:
  `process_gas_limit` reports `GasLimitExceeded` iff `burnt + charge > max_gas_burnt`
  (`gas_counter.rs:168-201`). With `prepaid` within one block's cost of 10^15, block-level and
  instruction-level metering report different variants. The PoC's `window` family hits exactly this case; an
  instruction-level ablation disagrees with nearcore on it (§10). Because of B10, this matters for the faithful
  `VMOutcome` but **not** for the outcome root.
* A trapping instruction has already been paid for when it traps (it is the last instruction of its range).

### 3.4 Not instrumented by finite-wasm, but limited elsewhere
Memory growth is limited by `StoreLimits` and the module maximum (2,048 pages): `memory.grow` past the limit
returns `-1` and does not trap, **after** paying its linear fee for the requested count (**[tested]**). Tables are
limited to 10,000 elements and 1 table.

## 4. Execution semantics actually executed

* **Determinism of numerics.** Integer ops follow the WASM spec. Floats are IEEE-754 with round-to-nearest-even
  (the default MXCSR, never changed by Winch) and canonical NaNs (B3). Under canonicalisation, every
  float result is a deterministic function of its inputs. The only WASM non-determinism (NaN payloads) is removed,
  and the canonical NaN has sign bit 0. **Hazard H3.** The test `W:mod.rs:1248-1291` masks the sign bit, so
  aarch64/Cranelift agreement on NaN *sign* is assumed rather than tested by nearcore. A Lean float spec can reuse the
  exact-rational approach of `spec/lean/v3/NearSpecV3/F64.lean`, but it needs the full range (subnormals,
  infinities, NaN), which F64.lean deliberately omits.
* **Saturating float→int** (`i32.trunc_sat_f64_s`, …) is enabled. The trapping `trunc` gives
  `WasmTrap(IllegalArithmetic)` on NaN or overflow (`BadConversionToInteger`, `W:mod.rs:393`).
* **Traps → `FunctionCallError`** (`W:mod.rs:381-413`, `trap_classification.rs`):

| Wasmtime trap | NEAR error |
|---|---|
| `MemoryOutOfBounds`, `TableOutOfBounds` | `WasmTrap(MemoryOutOfBounds)` |
| `IntegerDivisionByZero`, `IntegerOverflow`, `BadConversionToInteger` | `WasmTrap(IllegalArithmetic)` |
| `UnreachableCodeReached` | `WasmTrap(Unreachable)` |
| `IndirectCallToNull` | `WasmTrap(IndirectCallToNull)` |
| `BadSignature` | `WasmTrap(IncorrectCallIndirectSignature)` |
| `StackOverflow` (native) | `WasmTrap(StackOverflow)` |
| `Interrupt`, `HeapMisaligned`, unknown | `VMRunnerError` (node error, not an outcome) |
| GC/component/… traps | `panic!` (declared unreachable under NEAR's config) |
| host `VMLogicError::HostError(h)` | `HostError(h)` |
| instrumentation stack exhaustion | `HostError(MemoryAccessViolation)` |
| instrumentation gas exhaustion | `HostError(GasExceeded \| GasLimitExceeded)`, or `IntegerOverflow` on 128-bit overflow |

* **Native stack.** `max_wasm_stack` is set to 1 GiB (`W:mod.rs:510-511`) so that Wasmtime never traps before
  the instrumentation does. **Hazard H4.** Consensus then assumes that ≤ 262,144 accounted bytes of frames
  never overflow the *real* thread stack under Winch, whose frames are larger than the accounting suggests.
  A native overflow would be a `StackOverflow` trap or a crash, which differs from `MemoryAccessViolation`.
* **Gas hooks** (`W:mod.rs:1042-1072`): `CallingWasm`/`ReturningFromHost` set `GAS := prepaid − used`;
  `CallingHost`/`ReturningFromWasm` burn `remaining − GAS`. `ReturningFromWasm` also fires when wasm traps
  (`wasmtime-45.0.0/src/runtime/func.rs:1457-1482`), so gas consumed up to a trap is charged. **Hazard H5.** If
  that hook's `burn_gas` failed, the error would not be wrapped in `ErrorContainer`, so it would surface as
  `LinkError{msg}` (`W:mod.rs:369-420`). That is impossible while `prepaid ≤ max_gas_burnt`, which holds for every
  PV86 function call (`max_total_prepaid_gas = max_gas_burnt = 10^15`). The spec should carry this as an
  invariant.

## 5. Gas accounting (`logic/gas_counter.rs`)

* `burn_gas(x)` (`:147-166`): `new = burnt + x` (checked, `IntegerOverflow`); OK iff `new ≤ gas_limit`.
  Otherwise `process_gas_limit` (`:168-201`) sets `burnt := min(new, min(prepaid, max_gas_burnt))`,
  `promises_gas := min(prepaid, new_used) − burnt` (saturating), and returns `GasLimitExceeded` if
  `new > max_gas_burnt`, else `GasExceeded`.
* `pay_base`/`pay_per` (`:288-312`): `cost × n` checked (`IntegerOverflow` *without* burning), then `burn_gas`.
  Host functions pay **before** they bounds-check memory, so an out-of-bounds pointer still pays.
* `deduct_gas(burnt, used)` (`:118-140`) is the action variant used by promise/receipt-creating host functions.
  It also lowers `gas_limit` when gas is attached to promises.
* Wasm gas: §3.3. Host gas: Appendix A (the PV86 `ExtCosts` values are in Appendix A §3).
* Compute usage (`compute_usage`) differs from gas for the storage and trie costs (compute overrides in the
  snapshot). It feeds the chunk-level compute limit, so it is consensus-relevant through receipt scheduling.

## 6. Host functions

Appendix A has the complete PV86 inventory: 89 `env` imports grouped by category, with signature, gating flag, the
`ExtCosts` charged, semantic hazards and the live implementation line in `W:logic.rs`. It also covers the gas core
and the `HostError` → outcome mapping. The live implementation is `wasmtime_runner/logic.rs`, not
`logic/logic.rs` (Appendix A §0).

Host functions that read **trusted claim facts** (they matter for `InD3` and the claim, and are not computed from the witness):
`block_height`/`block_timestamp`/`epoch_height` (block header facts), `random_seed` (block randomness,
`context.random_seed`), `validator_stake`/`validator_total_stake` (epoch info), `chain_id`
(`runtime/runtime/src/ext.rs:338-340`). Storage host functions read the trie through `External`. Their
results **and gas** depend on the recorded-storage counter (`per_receipt_storage_proof_size_limit = 4,000,000`,
`logic/recorded_storage_counter.rs`, initialised at `W:mod.rs:343-346`), i.e. on witness recording. That
coupling must be part of `Rel`.

## 7. Outcome mapping

`VMOutcome{aborted, burnt_gas, used_gas, compute_usage, logs, return_data, …}` →
`runtime/runtime/src/function_call.rs` → `ActionResult`. `FunctionCallError` →
`ActionErrorKind::FunctionCallError(FunctionCallErrorSer)` (`runtime/runtime/src/conversions.rs:70-91`).
On abort, state changes and promises are discarded, logs are kept, and gas is burnt. The outcome root hashes
`PartialExecutionStatus`, which collapses every failure to `Failure` (B10). It also hashes logs,
receipt ids, gas burnt and tokens burnt.

## 8. Hazard register (things the spec must state as assumptions or model explicitly)

| # | Hazard | Proposed treatment |
|---|---|---|
| H1 | Compile success depends on Winch (x86_64) / Cranelift (aarch64) | assumption "every prepared module within limits compiles", tested on real and random contracts |
| H2 | Concurrency-permit `LinkError` | assumption (unreachable), documented |
| H3 | Canonical NaN sign on non-x86 | assumption, plus a per-opcode float difftest on x86_64 |
| H4 | Native stack overflow before the instrumented limit | assumption, plus a deep-recursion stress test at the 262,144 budget |
| H5 | Gas-hook burn failure becomes `LinkError` | invariant `prepaid ≤ max_gas_burnt` (prove it from the action-validation spec) |
| H6 | Error variants are not consensus-observable (B10) | `Rel` may quotient error kinds to the failure bit; the T evidence still compares exact errors |
| H7 | `bls12381_not_in_group_fix = false` at PV86: the known not-in-group behaviour is *protocol* | specify the buggy behaviour as is (Appendix A) |
| H8 | Storage-proof-size accounting couples execution to witness recording | model in `RuntimeD3` with the trie layer |

## 9. Alignment with the requirements contract §2.1

| §2.1 item | Where it is answered here |
|---|---|
| 1. validation + preparation + instrumentation, failures "exactly as nearcore" | §3, §2.3 (gas at PV86), B4/B5/B8 |
| 2. execution semantics, NaN/float determinism | §4, B2/B3 |
| 3. gas | §3.3, §5, Appendix A §3 |
| 4. host functions | §6, Appendix A |
| 5. integration into `Rel` | §1, §7 (full `RuntimeD3` integration is checkpoint 3 work) |

## 10. Checkpoint-1 PoC evidence

`examples/d3-wasm-poc/` (see its README) contains:
* `lean/`: a Lean 4 executable semantics (`WasmPoC`, no dependencies, no `sorry`/`axiom`; the only `partial`
  is in the stdin driver) covering decode → validate → finite-wasm gas and max-stack analyses → NEAR prologue,
  gas points and hooks → small-step execution → `value_return`/`panic` host functions → `VMOutcome` line;
* `../../oracle/wasm-d3/`: a Rust harness that runs the **same bytes** through pinned nearcore's
  `near_vm_runner::prepare` + `run` with the mainnet PV86 config (asserting `vm_kind == Wasmtime`);
* `gen_wasm.py`, a typed random generator, and `difftest.py`.

Results: 7,000 random modules, 0 disagreements; the instruction-level-metering ablation is caught (`examples/d3-wasm-poc/RESULTS.md`, strategy §5).

---

## Appendix A. Host-function inventory, gas core and error mapping at PV86

(Compiled from the pinned source; every row cites `W:logic.rs`. "W:" = `runtime/near-vm-runner/src/wasmtime_runner/`,
"L:" = `runtime/near-vm-runner/src/logic/`, "snap:" = the PV85 parameter snapshot. In this appendix, paths are
relative to the nearcore root.)


All paths are relative to the nearcore root. "W:" means `runtime/near-vm-runner/src/wasmtime_runner/`. "L:" means `runtime/near-vm-runner/src/logic/`. "snap:" means `core/parameters/src/snapshots/near_parameters__config_store__tests__85.json.snap`.

### 0. Which config and which implementation applies at PV86

**Config.** `STABLE_PROTOCOL_VERSION = 86` (`core/primitives-core/src/version.rs:628`). The config store has entries for 84 and 85, and the next one is 129 (`core/parameters/src/config_store.rs:62-64`). `get_config` returns the highest entry ≤ PV (`config_store.rs:240-247`), so PV86 uses the PV85 config. Its snapshot is `snap:` (wasm_config is at snap:108-260). `vm_kind` changed from NearVm to Wasmtime at PV84 (`core/parameters/res/runtime_configs/84.yaml:2`). PV85 turned on `one_yocto_on_promise`, `p256_verify_host_fn`, `gas_key_host_fns`, `chain_id_host_fn` and `yield_with_id_host_fns` (`85.yaml:1-5`). The snapshot confirms every flag value given in the task (snap:206-219), plus `discard_custom_sections=true` and `eth_implicit_global_contract=true`.

**How imports are declared and gated.** All imports are listed once, in the `imports!` invocation (`runtime/near-vm-runner/src/imports.rs:96-385`). The macro generates `for_each_available_import!($config, $M)` (`imports.rs:71-79`). Each entry can carry two kinds of gate:
- `#[config_field]` is a runtime gate. It expands to `if true && ($config).$config_field { M!(..) }` (`imports.rs:75`).
- `#[["feature"]]` is a compile-time `#[cfg(feature=..)]` gate (`imports.rs:74`).

Entries without `@in` go to module `env` (`imports.rs:59-61`). `@as gas:` exports `gas_seen_from_wasm` under the name `env.gas` (`imports.rs:56-58`, `imports.rs:345`). `@in internal:` entries go to module `internal` (`imports.rs:53-55`, `imports.rs:100-110`).

The runtime-gated entries are:
- `chain_id` (`imports.rs:121`)
- 4 global-contract actions (`imports.rs:208-211`)
- 3 gas-key actions (`imports.rs:265-287`)
- `p256_verify` (`imports.rs:152`)
- 2 yield-with-id functions (`imports.rs:305,322`)

The compile-time-gated entries are `sandbox_debug_log` (feature `sandbox`) and `sleep_nanos`/`burn_gas` (feature `test_features`) (`imports.rs:373-384`). Production builds do not include them.

**Linking (Wasmtime).** `fn link` (`W:mod.rs:1127-1155`) calls `imports::for_each_available_import!(config, add_import)` (`W:mod.rs:1154`). For each import it defines a trampoline:
1. Fetch the guest memory (`get_memory`, `W:mod.rs:1113-1125`).
2. Split it into `(&mut [u8], &mut Ctx)` (`W:mod.rs:1142`).
3. Call `logic::$func(ctx, memory, args..)` (`W:mod.rs:1143`).
4. Wrap any `VMLogicError` in an `ErrorContainer` (`W:mod.rs:1145-1147`, `W:mod.rs:1096-1111`).
5. Register it with `linker.func_wrap("env"|"internal", name, ..)` (`W:mod.rs:1151`).

The linker is built and `instantiate_pre` is called per module when the module is loaded (`W:mod.rs:755-764`).

**What happens on an unknown or disabled import.** Preparation (`prepare::prepare_contract` → `prepare_v3`, because `vm_kind==Wasmtime`, `runtime/near-vm-runner/src/prepare.rs:28-29`) treats imports as follows:
- Any import whose module is not `"env"` fails with `PrepareError::Instantiate`.
- Table and global imports fail with `PrepareError::Instantiate`, memory imports with `PrepareError::Memory`, and tag imports with `PrepareError::Deserialization`.
- Function imports are not name- or type-checked ("TODO: validate imported function types here").

These rules are in `runtime/near-vm-runner/src/prepare/prepare_v3.rs:303-326`. The `internal` instrumentation imports are added only after this check (`prepare_v3.rs:430-433`, `instrument_v3.rs:694-725`), so contracts cannot import `internal.*`.

An `env` function that is unknown or disabled (flag false) is never linked. `linker.instantiate_pre` then fails with `wasmtime::UnknownImportError`, which `into_vm_error` maps to `FunctionCallError::LinkError { msg: "unknown or invalid import" }` (`W:mod.rs:414-419`). A signature mismatch also becomes a `LinkError`, with Wasmtime's message as `msg` (`W:mod.rs:417`). The `LinkError` is cached in the in-memory module cache (`W:mod.rs:757-764`). It is then returned as `PreparationResult::OutcomeAbort` (`W:mod.rs:915-918`), which produces `VMOutcome::abort`: the contract-loading fee has already been burnt, and the outcome is a failed `FunctionCallError::ExecutionError("Link Error: unknown or invalid import")` (`runtime/runtime/src/conversions.rs:82`).

**Which `logic.rs` runs at PV86.** The live implementation is **`W:logic.rs`**:
- `W:mod.rs:37` declares `mod logic;`, and the trampoline at `W:mod.rs:1143` calls `logic::$func`, which resolves to `wasmtime_runner/logic.rs`.
- `VMKind::Wasmtime` dispatches to `WasmtimeVM::new` (`runtime/near-vm-runner/src/runner.rs:216-217`), and `vm_kind` comes from `Parameter::VmKind` (`core/parameters/src/parameter_table.rs:450`), which is Wasmtime from PV84 on (`84.yaml:2`).
- `L:logic.rs`'s `VMLogic` methods are instantiated only by the NearVM runner (`runtime/near-vm-runner/src/near_vm_runner/runner.rs:747`) and by tests.

However, `L:logic.rs` is still partly live through shared types. `W:logic.rs:10` does `use crate::logic::logic::*`, which pulls in:
- `Result` (`L:logic.rs:33`)
- `ExecutionResultState`, including `deduct_balance`, the log limits and `compute_outcome` (`L:logic.rs:38-155`)
- `Promise` (`L:logic.rs:197-200`)
- `PublicKeyBuffer` (`L:logic.rs:233-259`)
- `GlobalContractIdentifierPtrData` (`L:logic.rs:4566`)
- `VMOutcome::{abort, ok, nop_outcome, abort_but_nop_outcome_in_old_protocol}` (`L:logic.rs:4479-4540`)

The two copies of the host-function bodies are line-for-line equivalent in charging order. For example, the BLS macro in `L:bls12381.rs:27-60` matches `W:logic.rs:33-83`, and `storage_read` in both uses `deref(&mut FreeGasCounter)` (`L:logic.rs:4206`, `W:logic.rs:4600`).

### 1. Counts

- **Contract-importable functions at PV86 (module `env`, production build): 89.** That is 76 always-on entries plus 13 entries behind runtime flags, all of which are true at PV86. The count includes `env.gas` and the 3 deprecated iterator stubs.
- **Also linked, but not importable by contracts:** 11 `internal.finite_wasm_*` functions (`imports.rs:100-110`).
- **Excluded from production builds:** 3 compile-time-gated functions (`sandbox_debug_log`, `sleep_nanos`, `burn_gas`).

### 2. Inventory table

Notation used in the table:

| Abbreviation | Meaning |
|---|---|
| **i64 / i32** | Wasm types. Rust `u64` maps to i64 and `u32` to i32. |
| **base** | `ExtCosts::base`, charged per call. |
| **RM(n)** | `read_memory_base + read_memory_byte×n` (`W:logic.rs:93-102`). The fee is charged *before* the bounds check, so an out-of-bounds read still pays and then fails with `MemoryAccessViolation`. |
| **GMR(n)** | `get_memory_or_register` (`W:logic.rs:134-146`). If `len==u64::MAX`, it reads *register* `ptr` and charges `read_register_base + read_register_byte×len` (`L:vmstate.rs:137-150`). Otherwise it charges RM(len). |
| **WR(n)** | `Registers::set`: `write_register_base + write_register_byte×n` (`L:vmstate.rs:166-222`). It is subject to the register limits. |
| **WRrc** | `set_rc_data`: `write_register_base` only, with no per-byte charge (`L:vmstate.rs:184-192, 208-210`). |
| **WM16** | `write_memory_base + 16×write_memory_byte`, a u128 written little-endian into guest memory (`W:logic.rs:112-121, 174-177`). |
| **U128** | Reading a u128 from guest memory = RM(16) (`W:logic.rs:168-172`). |
| **AID(n)** | Account-id read: `GMR(n) + utf8_decoding_base + utf8_decoding_byte×n`, then strict parsing, because `account_id_validity_rules_version=2` (snap:256). An invalid id raises `InvalidAccountId` (`W:logic.rs:4416-4441`). |
| **UTF8(n)** | `utf8_decoding_base`, then RM(n) or a NUL-scan when `len==u64::MAX` (each byte costs `read_memory_base+read_memory_byte`), then `utf8_decoding_byte×n` (`W:logic.rs:392-427`). |
| **UTF16(n)** | Same pattern with `utf16_*` (`W:logic.rs:454-508`). |
| **ACT(x)** | Action fee through `pay_action_base` / `pay_action_per_byte`. Burnt = `send_fee(sir)` and used = send + exec; these are not ExtCosts (`W:logic.rs:4850-4881`). |
| **RCPT(deps)** | `pay_gas_for_new_receipt`: `new_action_receipt` send(sir) plus, for each data dependency, `new_data_receipt_base` send+exec, all of which is burnt. Used additionally includes `new_action_receipt` exec (`W:logic.rs:2011-2031`). |
| **TTN** | Trie-node charges from `External`: `touching_trie_node × db_reads + read_cached_trie_node × mem_reads` (`runtime/runtime/src/ext.rs:697-718`, `L:gas_counter.rs:399-407`). |
| **PIV** | Raises `ProhibitedInView` in view calls. This check always comes *after* `base` is charged. |

"Hazards" lists whether the function reads guest memory, writes guest memory or registers, touches the trie or external state, depends on block or environment data, or can fail through gas limits. No host function takes or returns floats. Every row's signature uses only i64/i32.

#### Registers
| name | wasm sig | PV86 gate | ExtCosts charged | hazards / notes | impl |
|---|---|---|---|---|---|
| read_register | (i64 register_id, i64 ptr)→() | always | base; read_register_base + read_register_byte×len; write_memory_base + write_memory_byte×len | Writes guest memory. Raises `InvalidRegisterId` if the register is absent. An out-of-bounds write raises `MemoryAccessViolation` after the gas is charged. | W:logic.rs:318 |
| register_len | (i64)→i64 | always | base | Returns `u64::MAX` if the register is absent. Pure. | W:logic.rs:336 |
| write_register | (i64 id, i64 data_len, i64 data_ptr)→() | always | base; RM(len); WR(len) | Reads memory, writes a register. Register limits apply (see §3). | W:logic.rs:354 |

#### Context / environment
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| current_account_id | (i64 reg)→() | always | base; WR(len) | Writes a register. | W:logic.rs:557 |
| chain_id | (i64 reg)→() | `chain_id_host_fn` (true) | base; WR(len) | Environment-dependent: `ext.chain_id()` returns `epoch_info_provider.chain_id()` (`runtime/runtime/src/ext.rs:338-340`). | W:logic.rs:576 |
| signer_account_id | (i64)→() | always | base; WR | PIV. | W:logic.rs:600 |
| signer_account_pk | (i64)→() | always | base; WR | PIV. Writes borsh-encoded public key bytes. | W:logic.rs:628 |
| predecessor_account_id | (i64)→() | always | base; WR | PIV. | W:logic.rs:656 |
| refund_to_account_id | (i64)→() | always (ungated) | base; WR | PIV. | W:logic.rs:686 |
| input | (i64)→() | always | base; WRrc (no per-byte charge) | Writes a register. The register still counts against size and memory limits. | W:logic.rs:710 |
| block_index | ()→i64 | always | base | Block-dependent (`context.block_height`). | W:logic.rs:729 |
| block_timestamp | ()→i64 | always | base | Block-dependent (ns). | W:logic.rs:739 |
| epoch_height | ()→i64 | always | base | Block-dependent. | W:logic.rs:749 |
| storage_usage | ()→i64 | always | base | Returns `result_state.current_storage_usage`, which `storage_write`/`storage_remove` mutate during the call. | W:logic.rs:805 |
| current_contract_code | (i64 reg)→i64 | always (ungated) | base; WR(32 or account-id len) | Returns 0 (None), 1 (Local hash), 2 (Global hash) or 3 (GlobalByAccount id), and writes the register on 1–3. | W:logic.rs:4366 |

#### Economics
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| account_balance | (i64 balance_ptr)→() | always | base; WM16 | Writes guest memory. The value is `account_balance + attached_deposit` minus amounts already deducted in this call (`L:logic.rs:66-70, 89-93`). | W:logic.rs:820 |
| account_locked_balance | (i64)→() | always | base; WM16 | Writes guest memory. | W:logic.rs:835 |
| attached_deposit | (i64)→() | always | base; WM16 | Writes guest memory. Allowed in view calls. | W:logic.rs:855 |
| prepaid_gas | ()→i64 | always | base | PIV. | W:logic.rs:874 |
| used_gas | ()→i64 | always | base | PIV. Returns burnt + promise gas. The value depends on the exact instrumentation and metering points (the call hook syncs the gas global before the call, `W:mod.rs:1049-1061`). | W:logic.rs:891 |

#### Math / crypto
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| random_seed | (i64 reg)→() | always | base; WR(32) | Block/receipt-dependent (`context.random_seed`). | W:logic.rs:1479 |
| sha256 | (i64 len, i64 ptr, i64 reg)→() | always | sha256_base; GMR(len); sha256_byte×len; WR(32) | Reads memory or a register, writes a register. | W:logic.rs:1499 |
| keccak256 | (i64,i64,i64)→() | always | keccak256_base; GMR; keccak256_byte×len; WR(32) | Same as sha256. | W:logic.rs:1537 |
| keccak512 | (i64,i64,i64)→() | always | keccak512_base; GMR; keccak512_byte×len; WR(64) | Same as sha256. | W:logic.rs:1575 |
| ripemd160 | (i64,i64,i64)→() | always | ripemd160_base; GMR; ripemd160_block×((len+8)/64+1); WR(20) | Per *block*, not per byte. | W:logic.rs:1615 |
| ecrecover | (i64 hash_len, i64 hash_ptr, i64 sig_len, i64 sig_ptr, i64 v, i64 malleability_flag, i64 reg)→i64 | always | ecrecover_base; GMR(sig); GMR(hash); WR(64) on success | Raises `ECRecoverError` if sig≠64 bytes, v≥4, hash≠32 bytes, or flag∉{0,1}. Returns 0 if the signature values are invalid or recovery fails, 1 on success. | W:logic.rs:1668 |
| ed25519_verify | (i64 sig_len, i64 sig_ptr, i64 msg_len, i64 msg_ptr, i64 pk_len, i64 pk_ptr)→i64 | always | ed25519_verify_base; GMR(sig); GMR(msg); ed25519_verify_byte×msg_len; GMR(pk) | Raises `Ed25519VerifyInvalidInput` if sig≠64 or pk≠32. Returns 0 if `sig[63]&0xE0≠0`, the key is invalid, or verification fails. | W:logic.rs:1783 |
| p256_verify | (same 6×i64)→i64 | `p256_verify_host_fn` (true) | p256_verify_base; GMR(sig); GMR(msg); p256_verify_byte×msg_len; GMR(pk) | Raises `P256VerifyInvalidInput` if sig≠64 or pk≠33 (compressed SEC1). Uses `verify_prehash`, so the message is treated as a prehash. Parse or verify failure returns 0. | W:logic.rs:1884 |
| alt_bn128_g1_multiexp | (i64,i64,i64)→() | always | alt_bn128_g1_multiexp_base; GMR; …_element×n; WR | Raises `AltBn128InvalidInput` (`L:alt_bn128.rs:18-21`). The element count comes from the parsed data. | W:logic.rs:932 |
| alt_bn128_g1_sum | (i64,i64,i64)→() | always | alt_bn128_g1_sum_base; GMR; …_element×n; WR | Same as g1_multiexp. | W:logic.rs:982 |
| alt_bn128_pairing_check | (i64,i64)→i64 | always | alt_bn128_pairing_check_base; GMR; …_element×n | Returns a bool (0/1). | W:logic.rs:1033 |
| bls12381_p1_sum | (i64,i64,i64)→i64 | always | bls12381_p1_sum_base; bls12381_p1_sum_element×(len/97); GMR; WR on success | No `base` charge in the code, despite what the doc comment says (`W:logic.rs:50-53`). The element charge comes *before* the memory read and uses the raw `value_len`: register mode (`u64::MAX`) causes a huge charge, so it fails with IntegerOverflow or a gas error. Raises `BLS12381InvalidInput` if len%97≠0 (`L:bls12381.rs:438-445`). Returns 0 on success, 1 on an invalid point. Version 0, because `bls12381_not_in_group_fix=false` (`W:logic.rs:62-66`). | macro W:logic.rs:33-83, inst. 1056 |
| bls12381_p2_sum | same | always | …p2_sum_base/element×(len/193); GMR; WR | Same as p1_sum, item size 193. | inst. W:logic.rs:1101 |
| bls12381_g1_multiexp | same | always | …g1_multiexp_*×(len/128) | Item size 128. | inst. W:logic.rs:1147 |
| bls12381_g2_multiexp | same | always | …g2_multiexp_*×(len/224) | Item size 224. | inst. W:logic.rs:1192 |
| bls12381_map_fp_to_g1 | same | always | …map_fp_to_g1_*×(len/48) | Item size 48. | inst. W:logic.rs:1238 |
| bls12381_map_fp2_to_g2 | same | always | …map_fp2_to_g2_*×(len/96) | Item size 96. | inst. W:logic.rs:1276 |
| bls12381_pairing_check | (i64,i64)→i64 | always | bls12381_pairing_base; GMR; bls12381_pairing_element×(data.len/288) | Element count comes after the read. Returns 0 (pairing ok), 2 (pairing false) or 1 (invalid) (`L:bls12381.rs:329-383`). | W:logic.rs:1352 |
| bls12381_p1_decompress | (i64,i64,i64)→i64 | always | …p1_decompress_*×(len/48) | As p1_sum. | inst. W:logic.rs:1378 |
| bls12381_p2_decompress | same | always | …p2_decompress_*×(len/96) | As p1_sum. | inst. W:logic.rs:1422 |

#### Logs / misc / gas
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| value_return | (i64 len, i64 ptr)→() | always | base; GMR(len); for each output data receiver, ACT `new_data_receipt_byte` (send(sir)+exec)×len, all burnt | Raises `ReturnedValueLengthExceeded` above 4 MiB (snap:236). Sets `return_data`; the last call wins. Allowed in view calls. | W:logic.rs:4170 |
| panic | ()→() | always | base | Always raises `GuestPanic{"explicit guest panic"}`. | W:logic.rs:4228 |
| panic_utf8 | (i64 len, i64 ptr)→() | always | base; UTF8(len) | Raises `GuestPanic{msg}`, or `BadUTF8` / `TotalLogLengthExceeded` / `MemoryAccessViolation`. `len=u64::MAX` means a NUL-terminated string. | W:logic.rs:4244 |
| log_utf8 | (i64,i64)→() | always | base; UTF8(len); log_base; log_byte×len | Raises `NumberOfLogsExceeded` at 100 logs (checked first) and `TotalLogLengthExceeded` at 16384 bytes (snap:228-229). Logs are part of the outcome hash (`core/primitives/src/transaction.rs:746-751`). | W:logic.rs:4267 |
| log_utf16 | (i64,i64)→() | always | base; UTF16(len); log_base; log_byte×utf8_len | Raises `BadUTF16` on an odd length or invalid UTF-16. | W:logic.rs:4291 |
| abort | (i32 msg_ptr, i32 filename_ptr, i32 line, i32 col)→() | always | base; 2×RM(4); 2×UTF16; log_base; log_byte×len | AssemblyScript ABI. Raises `BadUTF16` if a pointer is below 4. Pushes an `"ABORT: …"` log, then raises `GuestPanic`. | W:logic.rs:4316 |
| gas (`env.gas` → `gas_seen_from_wasm`) | (i32 opcodes)→() | always | none (burns opcodes×`regular_op_cost`; profiled as wasm gas) | Callable by contracts. It only burns gas (`W:logic.rs:1963-1968`). | W:logic.rs:1982 |

#### Promises (creation / DAG)
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| promise_create | (i64 acc_len, i64 acc_ptr, i64 m_len, i64 m_ptr, i64 a_len, i64 a_ptr, i64 amount_ptr, i64 gas)→i64 | always | `promise_batch_create` + `promise_batch_action_function_call` | Composite of those two functions. | W:logic.rs:2052 |
| promise_then | (i64 promise_idx + same 8)→i64 | always | `promise_batch_then` + `function_call` | Composite of those two functions. | W:logic.rs:2098 |
| promise_and | (i64 idx_ptr, i64 count)→i64 | always | base; promise_and_base; promise_and_per_promise×(count×8), which is per *byte* despite the name; RM(count×8) | PIV. Raises `InvalidPromiseIndex`, `NumberInputDataDependenciesExceeded` (128), `NumberPromisesExceeded` (1024), and IntegerOverflow on count×8. | W:logic.rs:2152 |
| promise_batch_create | (i64,i64)→i64 | always | base; AID; RCPT([]) | PIV. Creates an outgoing receipt (`ext.create_action_receipt`). Raises `NumberPromisesExceeded`. | W:logic.rs:2222 |
| promise_batch_then | (i64 idx, i64,i64)→i64 | always | base; AID; RCPT(one dependency per receipt) | PIV. Raises `InvalidPromiseIndex`. | W:logic.rs:2271 |
| promise_set_refund_to | (i64 idx, i64 len, i64 ptr)→() | always | base; AID | PIV. Raises `CannotSetRefundToOnJointPromise`. | W:logic.rs:2326 |
| promise_return | (i64 idx)→() | always | base; promise_return | PIV, checked *after* both charges. Raises `InvalidPromiseIndex` or `CannotReturnJointPromise`. | W:logic.rs:4134 |

#### Promise batch actions
| name | sig | gate | ExtCosts / fees | hazards / notes | impl |
|---|---|---|---|---|---|
| promise_batch_action_create_account | (i64)→() | always | base; ACT(create_account) | PIV. Raises `InvalidPromiseIndex` or `CannotAppendActionToJointPromise` (`W:logic.rs:2365-2381`). | W:logic.rs:2397 |
| promise_batch_action_deploy_contract | (i64 idx, i64 len, i64 ptr)→() | always | base; GMR(len); ACT(deploy_contract_base); ACT(deploy_contract_byte×len) | PIV. Raises `ContractSizeExceeded` above 4 MiB. | W:logic.rs:2439 |
| promise_batch_action_deploy_global_contract | (i64,i64,i64)→() | `global_contract_host_fns` (true) | base; GMR; ACT(deploy_global_contract_base); ACT(deploy_global_contract_byte×len) | PIV. Mode = CodeHash. | W:logic.rs:2504 (impl 2557) |
| promise_batch_action_deploy_global_contract_by_account_id | (i64,i64,i64)→() | `global_contract_host_fns` | same | Mode = AccountId. | W:logic.rs:2539 (impl 2557) |
| promise_batch_action_use_global_contract | (i64 idx, i64 hash_len, i64 hash_ptr)→() | `global_contract_host_fns` | base; GMR(32); ACT(use_global_contract_base); ACT(use_global_contract_byte×id_len) | PIV. Raises `ContractCodeHashMalformed` if the hash is not 32 bytes. | W:logic.rs:2621 (impl 2671) |
| promise_batch_action_use_global_contract_by_account_id | (i64,i64,i64)→() | `global_contract_host_fns` | base; AID; same ACTs | PIV. | W:logic.rs:2655 (impl 2671) |
| promise_batch_action_state_init | (i64 idx, i64 code_len, i64 code_ptr, i64 amount_ptr)→i64 | always (ungated) | base; GMR (32-byte code hash); U128; ACT(deterministic_state_init_base) | PIV. Raises `ContractCodeHashMalformed`, and `BalanceExceeded` from `deduct_balance`. Returns the action index. The import parameter names say "code" but the value must be a 32-byte hash. | W:logic.rs:2757 (impl 2815) |
| promise_batch_action_state_init_by_account_id | (i64 idx, i64 acc_len, i64 acc_ptr, i64 amount_ptr)→i64 | always | base; AID; U128; ACT(deterministic_state_init_base) | Same as state_init. | W:logic.rs:2797 (impl 2815) |
| set_state_init_data_entry | (i64 idx, i64 action_index, i64 k_len, i64 k_ptr, i64 v_len, i64 v_ptr)→() | always | base; GMR(k); GMR(v); ACT(deterministic_state_init_entry); ACT(deterministic_state_init_byte×(k+v)) | PIV. Raises `InvalidActionIndex` / `DataEntryAlreadyExists` (`runtime/runtime/src/receipt_manager.rs:335-346`). | W:logic.rs:2867 |
| promise_batch_action_function_call | (i64 idx, i64 m_len, i64 m_ptr, i64 a_len, i64 a_ptr, i64 amount_ptr, i64 gas)→() | always | delegates with gas_weight=0 | See function_call_weight. | W:logic.rs:2942 |
| promise_batch_action_function_call_weight | (above + i64 gas_weight)→() | always | base; U128; GMR(m); GMR(a); ACT(function_call_base); ACT(function_call_byte×(m+a)); prepay_gas(gas) | PIV. Raises `EmptyMethodName`, `InvalidMethodName` (non-UTF-8, `receipt_manager.rs:378-383`), `BalanceExceeded`, and `GasExceeded` from the prepay. One-yocto exemption: amount==1 and balance==0 adds to `subsidized_amount` (`W:logic.rs:3069-3080`). | W:logic.rs:3003 |
| promise_batch_action_transfer | (i64 idx, i64 amount_ptr)→() | always | base; U128; ACT(transfer), with implicit-account surcharges (`core/parameters/src/cost.rs:722-776`) | PIV. Raises `BalanceExceeded`. | W:logic.rs:3107 |
| promise_batch_action_stake | (i64 idx, i64 amount_ptr, i64 pk_len, i64 pk_ptr)→() | always | base; U128; GMR(pk); ACT(stake) | PIV. Raises `InvalidPublicKey`. ML-DSA keys are rejected unless post-quantum keys are enabled (`L:logic.rs:236-258`). | W:logic.rs:3398 |
| promise_batch_action_add_key_with_full_access | (i64 idx, i64 pk_len, i64 pk_ptr, i64 nonce)→() | always | base; GMR(pk); ACT(add_full_access_key) | PIV. Raises `InvalidPublicKey`. | W:logic.rs:3447 |
| promise_batch_action_add_key_with_function_call | (i64 idx, i64 pk_len, i64 pk_ptr, i64 nonce, i64 allowance_ptr, i64 recv_len, i64 recv_ptr, i64 names_len, i64 names_ptr)→() | always | base; GMR(pk); U128; AID(recv); GMR(names); ACT(add_function_call_key_base); ACT(add_function_call_key_byte×Σ(len+1)) | PIV. Raises `EmptyMethodName` (`L:utils.rs:11-20`), `InvalidMethodName` and `InvalidPublicKey`. | W:logic.rs:3500 |
| promise_batch_action_delete_key | (i64,i64,i64)→() | always | base; GMR(pk); ACT(delete_key) | PIV. | W:logic.rs:3596 |
| promise_batch_action_delete_account | (i64 idx, i64 len, i64 ptr)→() | always | base; AID; ACT(delete_account) | PIV. | W:logic.rs:3645 |
| promise_batch_action_transfer_to_gas_key | (i64 idx, i64 pk_len, i64 pk_ptr, i64 amount_ptr)→() | `gas_key_host_fns` (true) | base; GMR(pk); U128; ACT(gas_key_transfer_base); ACT(gas_key_byte) | PIV. `InvalidPublicKey` is raised *after* the fees are charged (`W:logic.rs:3212`). Raises `BalanceExceeded`. | W:logic.rs:3165 |
| promise_batch_action_add_gas_key_with_full_access | (i64 idx, i64 pk_len, i64 pk_ptr, i64 num_nonces)→() | `gas_key_host_fns` | base; GMR(pk); ACT(add_full_access_key); ACT(gas_key_nonce_write_base, exec only); ACT(gas_key_byte) (`L:gas_counter.rs:358-373`) | PIV. Raises IntegerOverflow if num_nonces > u16. | W:logic.rs:3233 |
| promise_batch_action_add_gas_key_with_function_call | (i64 idx, i64 pk_len, i64 pk_ptr, i64 num_nonces, i64 allowance_ptr, i64 recv_len, i64 recv_ptr, i64 names_len, i64 names_ptr)→() | `gas_key_host_fns` | add_key_with_function_call charges plus the gas-key fees | PIV. | W:logic.rs:3297 |

There is no `WithdrawFromGasKey` host function, by design (`imports.rs:288-292`).

#### Yield / resume
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| promise_yield_create | (i64 m_len, i64 m_ptr, i64 a_len, i64 a_ptr, i64 gas, i64 gas_weight, i64 reg)→i64 | always | base; yield_create_base; GMR(m); GMR(a); yield_create_byte×(m+a); prepay_gas(gas); RCPT([true]) with sir; ACT(function_call_base, sir); ACT(function_call_byte×(m+a)); WR(32 data_id) | PIV. Raises `EmptyMethodName`. Creates a yield receipt with a timeout of `yield_timeout_length_in_blocks=200` (snap:257, `runtime/runtime/src/function_call.rs:163-173`). | W:logic.rs:3720 |
| promise_yield_create_with_id | (i64 m_len, i64 m_ptr, i64 a_len, i64 a_ptr, i64 amount_ptr, i64 gas, i64 gas_weight, i64 yid_len, i64 yid_ptr)→i64 | `yield_with_id_host_fns` (true) | base; yield_create_with_id_base; U128; GMR(m); GMR(a); GMR(yield id); yield_create_byte×(m+a); then, if created: prepay, RCPT, ACT(function_call_base/byte) | PIV. Raises `YieldIdMalformed` (≠32 bytes). Returns `u64::MAX` without receipt charges if a yield with the same id is pending. Raises `BalanceExceeded`; the one-yocto exemption applies. | W:logic.rs:3805 |
| promise_yield_resume | (i64 data_id_len, i64 data_id_ptr, i64 payload_len, i64 payload_ptr)→i32 | always | base; yield_resume_base; yield_resume_byte×**raw payload_len** (charged before the read); GMR(id); GMR(payload) | PIV. Register mode for the payload (`u64::MAX`) raises IntegerOverflow in `pay_per`. Raises `YieldPayloadLength` (>1024, snap:258) and `DataIdMalformed`. Returns 1 or 0 (resumed or not). | W:logic.rs:3948 |
| promise_yield_resume_with_yield_id | (i64 yid_len, i64 yid_ptr, i64 payload_len, i64 payload_ptr)→i32 | `yield_with_id_host_fns` | same as promise_yield_resume | PIV. Raises `YieldIdMalformed`. | W:logic.rs:3997 |

#### Promise results
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| promise_results_count | ()→i64 | always | base | PIV. | W:logic.rs:4058 |
| promise_result | (i64 result_idx, i64 reg)→i64 | always | base; WRrc (no per-byte charge) | PIV. Returns 0 (NotReady), 1 (Successful, register written) or 2 (Failed). Raises `InvalidPromiseResultIndex`. | W:logic.rs:4091 |

#### Storage (trie)
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| storage_write | (i64 k_len, i64 k_ptr, i64 v_len, i64 v_ptr, i64 reg)→i64 | always | base; storage_write_base; GMR(k); GMR(v); storage_write_key_byte×k; storage_write_value_byte×v; TTN; storage_write_evicted_byte×old_len; WR(old) if evicted | PIV. Touches the trie (`ext.rs:147-187`, MemOrTrie lookup). Raises `KeyLengthExceeded` (2048), `ValueLengthExceeded` (4 MiB), and `RecordedStorageExceeded` (4,000,000 B, snap:259; `L:recorded_storage_counter.rs:19-32`). Updates storage_usage (+k+v+40 for a new record). Returns 1 if a value was evicted, else 0. | W:logic.rs:4464 |
| storage_read | (i64 k_len, i64 k_ptr, i64 reg)→i64 | always | base; storage_read_base; GMR(k); storage_read_key_byte×k; TTN; storage_read_value_byte×len; if len>4000 (`core/primitives-core/src/config.rs:14`), storage_large_read_overhead_base + _byte×len; WR(len) | Allowed in view calls. With FlatStorage mode the lookup is MemOrFlatOrTrie (`ext.rs:196-199`). Value deref is not TTN-charged (`FreeGasCounter`). Raises `KeyLengthExceeded` and `RecordedStorageExceeded`. Returns 1 or 0. | W:logic.rs:4564 |
| storage_remove | (i64 k_len, i64 k_ptr, i64 reg)→i64 | always | base; storage_remove_base; GMR(k); storage_remove_key_byte×k; TTN; storage_remove_ret_value_byte×old_len; WR(old) | PIV. Touches the trie (`ext.rs:233-272`). Updates storage_usage. | W:logic.rs:4639 |
| storage_has_key | (i64 k_len, i64 k_ptr)→i64 | always | base; storage_has_key_base; GMR(k); storage_has_key_byte×k; TTN | Allowed in view calls (`ext.rs:274-300`). | W:logic.rs:4705 |
| storage_iter_prefix | (i64,i64)→i64 | always (deprecated) | none | Always raises `Deprecated{storage_iter_prefix}`. | W:logic.rs:4768 |
| storage_iter_range | (i64,i64,i64,i64)→i64 | always (deprecated) | none | Always raises `Deprecated`. | W:logic.rs:4796 |
| storage_iter_next | (i64,i64,i64)→i64 | always (deprecated) | none | Always raises `Deprecated`. | W:logic.rs:4837 |

#### Validator
| name | sig | gate | ExtCosts | hazards / notes | impl |
|---|---|---|---|---|---|
| validator_stake | (i64 acc_len, i64 acc_ptr, i64 stake_ptr)→() | always | base; AID; validator_stake_base; WM16 | Epoch-dependent: `epoch_info_provider` (`ext.rs:326-330`). A provider error becomes `ExternalError`, which is a RuntimeError, not a user error. | W:logic.rs:760 |
| validator_total_stake | (i64 stake_ptr)→() | always | base; validator_total_stake_base; WM16 | Same as validator_stake (`ext.rs:332-336`). | W:logic.rs:788 |

#### Linked but not importable (module `internal`, instrumentation only)
| name | sig | behaviour | impl |
|---|---|---|---|
| finite_wasm_gas | (i64 gas)→() | `burn_gas(gas)`. Called inline when the gas global is below the region cost, so it always ends in a gas error. | W:logic.rs:182 |
| finite_wasm_gas_exhausted | ()→() | Burns all remaining gas and raises `HostError::IntegerOverflow`. Called on overflow in linear-fee arithmetic. | W:logic.rs:282 |
| finite_wasm_stack_exhausted | ()→() | Raises `HostError::MemoryAccessViolation`. Stack overflow is reported this way, not as `WasmTrap::StackOverflow`. | W:logic.rs:290 |
| finite_wasm_{memory,table}_{copy,fill,init}, finite_wasm_stack, finite_wasm_unstack | see `imports.rs:101-108` | Linked but **not referenced** by the v3 instrumentation, which only emits the 3 imports above (`instrument_v3.rs:694-725`). Linear fees and stack accounting are done inline. | W:logic.rs:193-280 |

### 3. Gas accounting core

**GasCounter fields and construction** (`L:gas_counter.rs`):
- Fields (`L:gas_counter.rs:65-82`):
  - `fast_counter.burnt_gas`
  - `fast_counter.gas_limit`
  - `promises_gas`
  - `max_gas_burnt`
  - `prepaid_gas`
  - `is_view`
  - `ext_costs_config`
  - `profile`
  - `send_action_compute_usage`
- `new` (`L:gas_counter.rs:85-108`): for view calls, `prepaid_gas` is set to `max_gas_burnt`. `gas_limit = min(max_gas_burnt, prepaid)`.
- In production, `max_gas_burnt` comes from `limit_config.max_gas_burnt`, or from `ViewConfig.max_gas_burnt` for views (`runtime/runtime/src/pipelining.rs:426-437`). `max_gas_burnt = max_total_prepaid_gas = 1 PGas` (snap:221, 230; changed in `83.yaml:7-9`).

**Charging primitives:**
- `pay_base(cost)` charges `burn_gas(cost.gas)` (`L:gas_counter.rs:305-315`).
- `pay_per(cost, n)` charges `burn_gas(cost.gas × n)`, using `checked_mul` and raising `IntegerOverflow` on overflow (`L:gas_counter.rs:290-302`).
- Both record only the delta actually burnt in the profile.
- `burn_gas` (`L:gas_counter.rs:147-166`) succeeds if `burnt + g ≤ gas_limit`. Otherwise it calls `process_gas_limit` (`L:gas_counter.rs:168-206`), which:
  - clamps `burnt` to `min(prepaid, max_gas_burnt)`
  - sets `promises_gas = min(prepaid, used) − burnt` (saturating)
  - returns `GasLimitExceeded` if `new_burnt > max_gas_burnt`, else `GasExceeded`.

**Burnt vs used:**
- `deduct_gas(burn, use)` asserts `burn ≤ use`. It adds `use − burn` to `promises_gas` and checks `burnt ≤ max_gas_burnt && burnt+promises ≤ prepaid`. When promise gas is added, it lowers `gas_limit` to `min(max_gas_burnt, prepaid − promises)` (`L:gas_counter.rs:118-142`).
- Action fees go through `pay_action_accumulated(burn_cost, use_gas, action)` (`L:gas_counter.rs:322-353`).
- `prepay_gas(g) = deduct_gas(0, g)`, which reserves gas for outgoing function calls (`L:gas_counter.rs:375-377`).
- `used_gas = promises + burnt` and `remaining_gas = prepaid − used` (`L:gas_counter.rs:384-391`).

**Compute usage:**
- `send_action_compute_usage` accumulates `burn_cost.compute` for actions. On a gas failure it accumulates the burnt gas instead (`L:gas_counter.rs:333-351`).
- At the end, `compute_outcome` (`L:logic.rs:131-154`):
  1. computes `wasm_gas = burnt − action_gas − host_gas` (`runtime/near-vm-runner/src/profile.rs:98-101`)
  2. sets `compute_usage = Σ_ext (profile_gas × compute/gas) + send_action_compute_usage + wasm_gas` (`profile.rs:144-175`). Wasm ops have compute = gas.
- Non-default ExtCosts compute values at PV86:
  - storage_write_base / storage_remove_base: 200e9 (`61.yaml:4-5`)
  - storage_read_base: 159e9; storage_read_key_byte: 10e6; storage_read_value_byte: 2.5e6 (`72.yaml:12-14`)
  - storage_has_key_base: 158e9; storage_has_key_byte: 10e6 (`72.yaml:10-11`)
  - storage_large_read_overhead_base: 41e9; storage_large_read_overhead_byte: 3,111,005 (`72.yaml:15-16`)
  - touching_trie_node / read_cached_trie_node: 4e9 (`82.yaml:5-11`)
  - All other ExtCosts have compute = gas.

**Contract loading:**
- `contract_loading_bytes × wasm_len + contract_loading_base` (`L:gas_counter.rs:224-227`).
- Because `fix_contract_loading_cost=false`, it is charged in `after_loading_executable` (`L:gas_counter.rs:259-272`; called at `W:mod.rs:804`), after compile/link. An empty method name fails first (`L:gas_counter.rs:241-246`).
- Missing or ill-typed methods return `abort_but_nop_outcome_in_old_protocol`, which is a **nop outcome with 0 gas** at PV86 (`W:mod.rs:887-902`, `L:logic.rs:4531-4540`).

**Instrumented wasm gas (finite-wasm inline counter, not Wasmtime fuel):**
- `prepare_v3` runs a `finite_wasm_6::Analysis` with `SimpleGasCostCfg { regular: regular_op_cost, linear_base: linear_op_base_cost, linear_unit: linear_op_unit_cost }` (`prepare_v3.rs:418-429`):
  - every operator costs `regular`
  - `block`, `end` and `else` cost 0
  - `memory.{init,copy,fill,grow}` and `table.{init,copy,fill,grow}` cost `linear_unit × count + linear_base` (`prepare_v3.rs:513-537`)
- `InstrumentContext::run` with import module `"internal"` (`prepare_v3.rs:430-457`) adds two mutable i64 globals, GAS and STACK, and exports the GAS global as `remaining_gas` (`instrument_v3.rs:727-745`).
- At each instrumentation point, the code checks `if $gas < C { call internal.finite_wasm_gas(C); unreachable } else { $gas -= C }`. Linear ops compute `count×linear+constant` with checked arithmetic that calls `finite_wasm_gas_exhausted` on overflow (`instrument_v3.rs:800-881`). Charges are taken at the *start* of each metered region (`instrument_v3.rs:607-619`).
- Function entry charges stack (`operand+frame` bytes against `max_stack_height=262144`, snap:222; on overflow it calls `finite_wasm_stack_exhausted`) and gas `ceil(frame/8)×regular_op_cost` (`instrument_v3.rs:561-597`).
- Synchronisation with GasCounter is done by a Wasmtime `store.call_hook` (`W:mod.rs:1042-1072`):
  - On `CallingHost` / `ReturningFromWasm`, it reads the global and calls `gas_counter.burn_gas(remaining_gas() − global)`.
  - On `ReturningFromHost` / `CallingWasm`, it sets `global = remaining_gas()`.
  - Wasmtime fuel is not used: `OutOfFuel` is classified as "unreachable under NEAR config" (`W:trap_classification.rs:47-48`).
- The `env.gas(opcodes)` import burns `opcodes × regular_op_cost` (`W:logic.rs:1963-1984`). It is a legacy import that the v3 instrumentation does not emit.
- At PV86: `regular_op_cost` = 822,756; `linear_op_base_cost` = 26,328,192; `linear_op_unit_cost` = 822,756; `grow_mem_cost` = 1 (snap:201-204). `grow_mem_cost` is unused by Wasmtime; memory.grow is charged through the linear fee.

**Memory and register charges and limits:**
- Guest reads cost `read_memory_base + read_memory_byte×len`, and writes cost `write_memory_base + write_memory_byte×len`. Both are charged before the bounds check (`W:logic.rs:93-121`). `get_u8` is used for the NUL scan (`W:logic.rs:148-154`).
- Register read: `read_register_base + byte×len` (`L:vmstate.rs:137-150`). Register write: `write_register_base + write_register_byte×len`; the per-byte part is omitted for `input` and `promise_result` (`L:vmstate.rs:194-222`).
- Register limits (`L:vmstate.rs:229-262`) all raise `MemoryAccessViolation`:
  - `max_register_size` = 104,857,600
  - `max_number_registers` = 100. The check is `len ≥ max` even when replacing an existing register, a documented protocol quirk.
  - `registers_memory_limit` = 1 GiB, counting Σ(len+8).
  - Limit values are at snap:225-227.
- Guest memory is 1024 initial / 2048 max pages (snap:223-224). It is defined in-module and exported as `memory` for Wasmtime (`prepare_v3.rs:126-139, 371-379`), and capped by `StoreLimits` (`W:mod.rs:321-339`).

**PV86 ExtCosts values (gas; from snap:110-199):**

| ExtCost | gas | ExtCost | gas |
|---|---|---|---|
| base | 264,768,111 | storage_read_base | 56,356,845,749 |
| contract_loading_base | 35,445,963 | storage_read_key_byte | 30,952,533 |
| contract_loading_bytes | 1,089,295 | storage_read_value_byte | 5,611,004 |
| read_memory_base | 2,609,863,200 | storage_large_read_overhead_base | 1 |
| read_memory_byte | 3,801,333 | storage_large_read_overhead_byte | 1 |
| write_memory_base | 2,803,794,861 | storage_remove_base | 53,473,030,500 |
| write_memory_byte | 2,723,772 | storage_remove_key_byte | 38,220,384 |
| read_register_base | 2,517,165,186 | storage_remove_ret_value_byte | 11,531,556 |
| read_register_byte | 98,562 | storage_has_key_base | 54,039,896,625 |
| write_register_base | 2,865,522,486 | storage_has_key_byte | 30,790,845 |
| write_register_byte | 3,801,564 | storage_iter_* (8 params) | 0 (unused; deprecated) |
| utf8_decoding_base | 3,111,779,061 | touching_trie_node | 2,280,000,000 |
| utf8_decoding_byte | 291,580,479 | read_cached_trie_node | 2,280,000,000 |
| utf16_decoding_base | 3,543,313,050 | promise_and_base | 1,465,013,400 |
| utf16_decoding_byte | 163,577,493 | promise_and_per_promise | 5,452,176 |
| sha256_base | 4,540,970,250 | promise_return | 560,152,386 |
| sha256_byte | 24,117,351 | validator_stake_base | 911,834,726,400 |
| keccak256_base | 5,879,491,275 | validator_total_stake_base | 911,834,726,400 |
| keccak256_byte | 21,471,105 | alt_bn128_g1_multiexp_base | 713,000,000,000 |
| keccak512_base | 5,811,388,236 | alt_bn128_g1_multiexp_element | 320,000,000,000 |
| keccak512_byte | 36,649,701 | alt_bn128_g1_sum_base | 3,000,000,000 |
| ripemd160_base | 853,675,086 | alt_bn128_g1_sum_element | 5,000,000,000 |
| ripemd160_block | 680,107,584 | alt_bn128_pairing_check_base | 9,686,000,000,000 |
| ed25519_verify_base | 210,000,000,000 | alt_bn128_pairing_check_element | 5,102,000,000,000 |
| ed25519_verify_byte | 9,000,000 | yield_create_base | 153,411,779,276 |
| ecrecover_base | 278,821,988,457 | yield_create_byte | 15,643,988 |
| p256_verify_base | 1,300,000,000,000 | yield_create_with_id_base | 290,000,000,000 |
| p256_verify_byte | 13,000,000 | yield_resume_base | 1,195,627,285,210 |
| log_base | 3,543,313,050 | yield_resume_byte | 47,683,715 |
| log_byte | 13,198,791 | bls12381_p1_sum_base / element | 16,500,000,000 / 6,000,000,000 |
| storage_write_base | 64,196,736,000 | bls12381_p2_sum_base / element | 18,600,000,000 / 15,000,000,000 |
| storage_write_key_byte | 70,482,867 | bls12381_g1_multiexp_base / element | 16,500,000,000 / 930,000,000,000 |
| storage_write_value_byte | 31,018,539 | bls12381_g2_multiexp_base / element | 18,600,000,000 / 1,995,000,000,000 |
| storage_write_evicted_byte | 32,117,307 | bls12381_map_fp_to_g1_base / element | 1,500,000,000 / 252,000,000,000 |
| | | bls12381_map_fp2_to_g2_base / element | 1,500,000,000 / 900,000,000,000 |
| | | bls12381_pairing_base / element | 2,130,000,000,000 / 2,130,000,000,000 |
| | | bls12381_p1_decompress_base / element | 15,000,000,000 / 81,000,000,000 |
| | | bls12381_p2_decompress_base / element | 15,000,000,000 / 165,000,000,000 |

The enum and discriminants are at `core/parameters/src/cost.rs:257-346`, and the parameter-name mapping at `cost.rs:402+`. `contract_compile_*` (0) appears only in the view.

Selected action fees, as send_sir / send_not_sir / exec (snap:7-90):

| Action | send_sir | send_not_sir | exec |
|---|---|---|---|
| new_action_receipt | 108,059,500,000 | 108,059,500,000 | 108,059,500,000 |
| new_data_receipt_base | 36,486,732,312 | 36,486,732,312 | 36,486,732,312 |
| new_data_receipt_byte | 17,212,011 | 47,683,715 | 17,212,011 |
| function_call | 200e9 | 200e9 | 780e9 |
| function_call_byte | 2,235,934 | 47,683,715 | 2,235,934 |
| create_account | 500e9 | 500e9 | 7.2e12 |
| transfer | 115,123,062,500 | 115,123,062,500 | 115,123,062,500 |

### 4. Errors

**HostError variants** (`L:errors.rs:215-364`), with the functions that raise them in the live implementation:

| Variant | Raised by |
|---|---|
| BadUTF16 | `get_utf16_string` (log_utf16, abort); abort with a pointer below 4 |
| BadUTF8 | UTF8 decoding (panic_utf8, log_utf8); account-id parsing |
| GasExceeded / GasLimitExceeded | Any charge, through `burn_gas` / `deduct_gas`; contract loading (`L:gas_counter.rs:248-251, 265-268`); `finite_wasm_gas` |
| BalanceExceeded | `deduct_balance`: function_call*, transfer*, state_init*, yield_create_with_id |
| EmptyMethodName | function_call*, yield_create*, `split_method_names` (add_*key_with_function_call) |
| GuestPanic | panic, panic_utf8, abort |
| IntegerOverflow | `pay_per` overflow; promise_and; action fee math; num_nonces>u16; finite_wasm_gas_exhausted |
| InvalidPromiseIndex | promise_and, promise_batch_then, promise_set_refund_to, promise_return, all batch actions |
| CannotAppendActionToJointPromise | All batch actions |
| CannotReturnJointPromise | promise_return |
| CannotSetRefundToOnJointPromise | promise_set_refund_to |
| InvalidPromiseResultIndex | promise_result |
| InvalidRegisterId | Register reads |
| MemoryAccessViolation | Out-of-bounds guest memory access; register limits; stack exhaustion; missing memory export (`W:mod.rs:1117-1119`) |
| InvalidReceiptIndex | `receipt_manager.rs:121` (internal invariant) |
| InvalidIteratorIndex | Not raised at PV86 (iterators are deprecated) |
| InvalidActionIndex | set_state_init_data_entry |
| InvalidAccountId | AID parsing |
| InvalidMethodName | Non-UTF-8 method names (`receipt_manager.rs:382, 500, 598`) |
| InvalidPublicKey | stake, add_key*, delete_key, gas-key functions |
| ProhibitedInView | All PIV functions |
| NumberOfLogsExceeded | log_utf8, log_utf16, abort |
| KeyLengthExceeded / ValueLengthExceeded | storage_* functions |
| TotalLogLengthExceeded | Logs and panic_utf8 / UTF-16 decoding |
| NumberPromisesExceeded | `checked_push_promise` (`W:logic.rs:516-528`) |
| NumberInputDataDependenciesExceeded | promise_and |
| ReturnedValueLengthExceeded | value_return |
| ContractSizeExceeded | deploy_contract, deploy_global_contract* |
| Deprecated | storage_iter_* |
| ECRecoverError | ecrecover |
| AltBn128InvalidInput | alt_bn128_* |
| Ed25519VerifyInvalidInput | ed25519_verify |
| P256VerifyInvalidInput | p256_verify |
| BLS12381InvalidInput | bls12381_* |
| YieldPayloadLength | yield_resume* |
| DataIdMalformed | promise_yield_resume |
| YieldIdMalformed | *_with_id functions |
| RecordedStorageExceeded | storage_write/read/remove/has_key, through `observe_size` |
| ContractCodeHashMalformed | use_global_contract, state_init |
| DataEntryAlreadyExists | set_state_init_data_entry |

`VMLogicError` (`L:errors.rs:366-374`) has three variants:
- `HostError(h)` becomes `FunctionCallError::HostError`.
- `ExternalError` becomes `VMRunnerError::ExternalError` (storage or validator failure).
- `InconsistentStateError` becomes `VMRunnerError::InconsistentStateError`.

The conversion is at `W:mod.rs:372-379`, with the same mapping in `L:errors.rs:412-421`.

**Wasmtime traps → FunctionCallError::WasmTrap** (`W:mod.rs:381-412`):

| Wasmtime trap | WasmTrap |
|---|---|
| StackOverflow | StackOverflow |
| MemoryOutOfBounds, TableOutOfBounds | MemoryOutOfBounds |
| IndirectCallToNull | IndirectCallToNull |
| BadSignature | IncorrectCallIndirectSignature |
| IntegerOverflow, IntegerDivisionByZero, BadConversionToInteger | IllegalArithmetic |
| UnreachableCodeReached | Unreachable |

Other traps:
- `Interrupt` and `HeapMisaligned` become `VMRunnerError::WasmUnknownError` ("nondeterministic trap").
- Traps classified as unreachable under NEAR's configuration cause a `panic!`.
- Unknown traps become `WasmUnknownError`.

The classification is in `W:trap_classification.rs:32-95`. Any other instantiation, link or start failure becomes `LinkError{msg}` (`W:mod.rs:414-419, 1019-1025`). A failure to acquire an execution slot becomes `LinkError{"failed to acquire execution slot"}` (`W:mod.rs:1012-1018`).

**VMOutcome:**
- An abort keeps the gas burnt so far and sets `aborted = Some(err)` (`L:logic.rs:4498-4502`, `W:mod.rs:1084-1093`).
- `nop_outcome` has 0 gas (`L:logic.rs:4511-4527`).

**Mapping in runtime/runtime:**

`execute_function_call` (`runtime/runtime/src/function_call.rs:292-339`) handles VM runner errors:

| VMRunnerError | Result |
|---|---|
| ContractCodeNotPresent | `nop_outcome(CompilationError::CodeDoesNotExist)`, or `StorageError::MissingTrieValue` during witness validation |
| ExternalError | `RuntimeError` (StorageError or ValidatorError); chunk application fails |
| InconsistentStateError, CacheError | `StorageError::StorageInconsistentState` |
| LoadingError | `nop_outcome(LoadingError)` |
| WasmUnknownError | `nop_outcome(WasmUnknownError)`; soft-fail with 0 gas |

`action_function_call` converts `outcome.aborted = Some(err)` (`function_call.rs:100-142`) into `ActionErrorKind::FunctionCallError(Convert::convert(err))` (`function_call.rs:139-141`), using `conversions.rs:70-91`:

| VM FunctionCallError | Primitives FunctionCallError |
|---|---|
| CompilationError | CompilationError (WasmtimeCompileError is relabelled WasmerCompileError, `conversions.rs:64`) |
| MethodResolveError | MethodResolveError |
| HostError(e) | `ExecutionError(e.to_string())` |
| WasmTrap(t) | `ExecutionError("WebAssembly trap: …")` (`L:errors.rs:458-470`) |
| LinkError | `ExecutionError("Link Error: …")` |
| LoadingError | `ExecutionError("Loading Error: …")` |
| WasmUnknownError | `ExecutionError(msg)` |

Gas burnt and used are still added to the action result (`function_call.rs:143-151`). `apply_action_receipt` maps the result to an execution status (`runtime/runtime/src/lib.rs:1122-1129`):
- `Err(e)` becomes `ExecutionStatus::Failure(TxExecutionError::ActionError(e))`.
- `Ok(Value)` becomes `SuccessValue`.
- `Ok(None)` becomes `SuccessValue([])`.
- `Ok(ReceiptIndex)` becomes `SuccessReceiptId`.

Only the failure *bit* enters the merkleized outcome: `PartialExecutionStatus::Failure` (`core/primitives/src/transaction.rs:597-612, 746-751`). Logs are hashed too, so the error text itself is not consensus-hashed.
