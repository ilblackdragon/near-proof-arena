# Clean-room NEAR PV86 WASM execution (D3α integer subset)

`nearwasm.py` is an independent implementation of NEAR contract execution at PV86 for the D3α subset. It uses
only the Python 3 standard library. Its inputs were limited to:
`docs/research/near-wasm-prose-spec.md` (the primary source), `docs/research/near-wasm-boundary.md` (Appendix A
host-function behaviour and parameter values), the WebAssembly 2.0 specification (from memory), and the I/O
format of `tests/*.py` and `src/main.rs`. It did **not** use the nearcore `prepare/` or `wasmtime_runner/`
sources, finite-wasm, or the Lean specification (`spec/lean/v3/NearSpecV3/Wasm`, `examples/d3-wasm-poc/lean`,
`oracle/wasm-d3/lean`), nor the git history of any of them.

Where the prose was silent or ambiguous, the answer came from **black-box runs** of the nearcore harness.
The probe scripts are in `probes/` (290 hand-built cases, all agreeing). One preparation detail, the
instrumented-size estimate, was fitted to the *lengths* of nearcore's prepared modules. The prepared bytes
were never inspected.

```
nearwasm.py [--charge-points] < cases      # `<prepaid> <wasm_hex> [<receiver>,...]` per line
difftest_cr.py (opcodes | random N SEED | promise N SEED | mutate N SEED) [--shards K] [--timeout S]
run_all.sh                                  # the five required families
```

## What is implemented

* **Decoding and validation.** WebAssembly 2.0 with NEAR's feature set: MVP, mutable globals,
  sign-extension, saturating float→int, reference types (funcref only) and bulk memory. LEB128 encodings are
  strict. Section order, sizes and counts are checked, as are the data-count rules, constant expressions,
  declared function references (elements, exports and globals) and the full operator typing. Float types
  and operators are type-checked, so preparation errors stay exact even for float modules. A float module
  that decodes successfully gets `out-of-domain`.
* **Every PrepareError variant, with 0 gas**, in nearcore's order. This includes `Serialization`, which
  the prose spec does not mention (defect D6), and `WasmtimeCompileError` for more than 49,998
  params+locals.
* **Charge points** (prose §2): liveness, branch targets, ranges, targeted and untargeted loops, bulk
  points, and the prologue. `--charge-points` prints `f<i>: pc:const:linear ...`. Here `i` is the index
  among *defined* functions, `pc` indexes the flat operator list (the final `end` included), and the
  prologue charge `⌈frame/8⌉·R` is **not** listed.
* **Operand-stack maximum** (§3), including the `call_indirect` quirk. Frame size, the stack budget and
  `MemoryAccessViolation` on exhaustion are also implemented.
* **Gas counter** (§4): the wasm-side copy `g`, syncs at host calls and on return or trap, `burn`,
  `deduct_gas` (burn/use split, with the limit lowered by promise gas), the clamping rules, and
  `GasExceeded` versus `GasLimitExceeded`. Also covered: the loading fee, link resolution, and method
  resolution.
* **Execution.** All i32/i64 integer operators, including sign-extension. Also all loads and stores,
  `memory.size`/`memory.grow` (1,024 pages initially, at most 2,048), bulk memory, globals, tables
  (capped at 10,000 entries), the `ref.*` operators, `call_indirect` (including host functions reached
  through a table), element and data segments (forms 0–7 and 0–2), instantiation traps, the start function
  (which may be an import), and the trap mapping.
* **Host functions:** `value_return` (with output data receivers), `panic`, `gas`, `promise_batch_create`
  and `promise_batch_action_function_call` (including the one-yocto exemption). All 89 PV86 `env` imports
  are known for linking, with their signatures from Appendix A. Calling any other host function prints
  `unmodeled host function <name>`.

## Agreement with nearcore (final run)

| family | cases | compared | out-of-domain | unmodeled | skipped (>20 s) | disagreements |
|---|---|---|---|---|---|---|
| opcodes (`opcases.py`) | 9,167 | 9,166 | 1 (`float-local`) | 0 | 0 | **0** |
| random 2000 seed 1 | 2,000 | 2,000 | 0 | 0 | 0 | **0** |
| random 2000 seed 2 | 2,000 | 2,000 | 0 | 0 | 0 | **0** |
| promise 2000 seed 1 | 2,000 | 2,000 | 0 | 0 | 0 | **0** |
| mutate 5000 seed 11 | 5,000 | 4,998 | 2 | 0 | 0 | **0** |

Extra runs, all with 0 disagreements and 0 skips:
* random 2000, seeds 3, 4 and 5;
* promise 2000 seed 2, and promise 4000 seed 3;
* mutate 20000, seeds 12, 13 and 14 (5–7 out-of-domain each);
* 290 hand-built probes (`probes/p2.py` … `p12.py`).

No case needed the 20 s skip. The whole required set runs in about 80 s on 16 cores.

The comparison uses the same normalisation as `tests/difftest.py`: the text of Wasmtime's mistyped-import
`LinkError` message and of `WasmtimeCompileError` is not compared. The implementation does reproduce both
formats.

## Defects and gaps in the prose spec (each resolved by nearcore's behaviour)

**D1. Linking is missing entirely (§4).** The prose never mentions `LinkError`.
* An `env` import whose name is not one of the 89 host functions gives
  `LinkError { msg: "unknown or invalid import" }`. A wrong signature gives a Wasmtime
  `types incompatible: expected type ..., found type ...` message.
* Both are charged the loading fee. Linking needs the host inventory and its signatures, which come only
  from the boundary doc.
* The order is: loading fee → link → method resolution → instantiation (element, then data segments) →
  start → `main`.
* A loading-fee failure therefore beats both `LinkError` and the "0-gas `MethodResolveError`". With a
  missing `main` and too little gas, the outcome is `GasExceeded` with burnt = prepaid, not 0.
* Method resolution comes before instantiation traps: a missing `main` plus an out-of-bounds data segment
  gives `MethodNotFound` with 0 gas.
* An export named `main` that is a memory, table or global gives `MethodNotFound`.
* `main` may be an exported import (for example `env.panic`), and the start function may be an import.
  Both call the host function directly.

**D2. Block types (§1, "multi-value invalid").**
* *Every* type-index block type is rejected, including `[]→[]` and `[]→[t]`, which a reading of
  "multi-value disabled" in WebAssembly 2.0 terms would allow.
* Non-canonical multi-byte s33 encodings of `0x40` or of a value type are also rejected.
* In effect, a block type is a single byte: `0x40`, `i32`, `i64`, `f32`, `f64` or `funcref`.

**D3. Function-count check order (§1, item 2).** `imports + bodies > 10,000 → TooManyFunctions` uses
the code section's *declared* count. It is checked *before* that count is compared with the function
section, so a corrupted count gives `TooManyFunctions`, not `Deserialization`. A function section that
declares more than 10,000 functions but has no code section gives `Deserialization`.

**D4. `TooManyLocals` is a parse-time check (§1, item 2; the prose lists it after "parse and validate").**
* For each body, in order:
  1. the size check (`FunctionBodyTooLarge`);
  2. the local declarations, read group by group with a running contract total
     (`> 1,000,000 → TooManyLocals` after each group);
  3. validation of that body: local types, the 50,000 params+locals limit, operators.
* Local types are parsed *permissively* at step 2. Any syntactically valid value type passes, including
  `externref`, `v128`, `(ref null ...)` and concrete type indices. An unparsable byte such as `0x40`
  fails as `Deserialization` at its own group.
* Consequences: a single body declaring 2,000,001 locals gives `TooManyLocals`, not `Deserialization`. The
  same holds for `(1 × externref), (2,000,001 × i32)`.
* Earlier bodies are fully validated before later bodies' NEAR checks: an invalid operator in body 1 beats
  `FunctionBodyTooLarge` or `TooManyLocals` in body 2.

**D5. Wrong or missing implementation limits (§1, item 1).**
* Table sizes have **no** parser limit below `u32`. A table with an initial size of 10,000,001 gives
  `TooManyTableElements`, not `Deserialization`. A maximum of `2^32−1` is accepted.
* Memories are limited to 65,536 pages, for both initial and maximum.
* Type section: results are also limited to 1,000, but multi-value already rejects more than 1.

**D6. `PrepareError::Serialization` is missing.**
* A non-memory export whose name is exactly 100,000 bytes is valid, but NEAR renames it to `"\0" ++ name`.
  At 100,001 bytes, the instrumentation's re-parse fails.
* The result is `Serialization`, after all decoding and validation but before every check in §1 item 3 and
  before `WasmtimeCompileError`.
* Memory exports are exempt, because they are removed. Import names are not renamed: a 100,000-byte
  import name gives a `LinkError`.

**D7. `InstrumentedCodeTooLarge` cannot be computed from the prose (§1, item 4).** The instrumented
module's encoding is not specified. `nearwasm.py` uses a linear estimate fitted to nearcore's
prepared-module lengths, with a maximum relative error of 0.7%. It prints `unmodeled` when the estimate is
within 1.5% of 16 MiB. A real fix is to specify the size formula, or to state the size bound over the
original module.

**D8. Encoding deviations from "WebAssembly 2.0 rules" (§1, item 1).** "WebAssembly 2.0 rules" is not
precise enough, because nearcore uses the newer parser encodings:
* LEB `u32` indices, so a non-canonical `0x80 0x00` is accepted: the memory indices of `memory.copy`,
  `memory.fill` and `memory.init`, every table index of `table.*`, and the element and data indices.
  (In WebAssembly 2.0, the `memory.*` reserved operands are single `0x00` bytes.)
* Single `0x00` bytes, so `0x80 0x00` is rejected: the reserved byte of `memory.size`/`memory.grow`, and
  **the table index of `call_indirect`**. (WebAssembly 2.0 encodes the `call_indirect` table index as an
  LEB `u32`, so it would accept `0x80 0x00`.)
* A memarg with flag bit 6 set (the multi-memory form) is rejected even with memory index 0. Memarg
  offsets are `u32`.
* Element segments of forms 4–7 accept only `ref.null func` and `ref.func`; `global.get` is rejected
  because global imports are banned. A global initializer may not use `global.get` of a defined global.
* Custom-section names must be valid UTF-8, and an empty custom section is invalid.
* Section ids 13 and above are invalid.

**D9. Import section order (§1, item 2).** The whole import section is parsed and validated first: a bad
type index, a truncated entry or a tag import after an `other`-module import gives `Deserialization`. The
NEAR checks then run per import, in order:
1. module ≠ `env` → `Instantiate`;
2. memory → `Memory`;
3. table or global → `Instantiate`;
4. running count of function imports > 10,000 → `TooManyFunctions`.

The first failing import decides. The table section works the same way: whole-section validation, then
`TooManyTables`, then `TooManyTableElements`.

**D10. Per-function checks (§1, item 3), clarifications.** The order is confirmed as written: params,
contract params, operand stack, blocks, contract blocks, function by function.
* Imported functions count toward neither params limit. An import with 65 params is fine at preparation
  time and then fails to link.
* `block`, `loop` and `if` in dead code *do* count toward the block limits, while dead code is ignored for
  the operand stack.

**D11. Host-function check order (Appendix A gives the charges, not the order of checks).** Resolved by
probes:
* **`promise_batch_action_function_call`:** `base` → read amount (RM 16) → read method (GMR) →
  `EmptyMethodName` → read args (GMR) → `InvalidPromiseIndex` → `ACT(function_call)` →
  `ACT(function_call_byte × (m+a))` → `prepay_gas(gas)` → balance check.
  * The prepay happens **before** `BalanceExceeded`, so `used` includes the attached gas. A failing
    prepay beats `BalanceExceeded`.
  * The one-yocto exemption: when the balance is already 0, an amount of 1 succeeds and leaves the balance
    at 0.
  * `gas = u64::MAX` gives `IntegerOverflow`.
* **`promise_batch_create`:** `base` → account-id read → `utf8_decoding_base` + `utf8_decoding_byte·n` →
  UTF-8 check (`BadUTF8`) → account-id validity (`InvalidAccountId`, including an empty id) →
  `new_action_receipt` fee → `NumberPromisesExceeded`. The receipt fee is paid before the limit check
  fails.
* **`value_return`:** `base` → read → `ReturnedValueLengthExceeded` → receiver fees. The length check comes
  before the per-receiver `new_data_receipt_byte` fees.
* **Register path** (`len = u64::MAX`, no registers exist): `InvalidRegisterId { register_id: ptr }` is
  raised after `base` and **without** any `read_register` charge.
* **Pointer overflow:** a `ptr + len` that overflows gives `MemoryAccessViolation` after the read charges.

**D12. `deduct_gas` failure semantics are not in prose §4.** Action fees and prepaid gas fail like `burn`,
with `new_burnt = burnt + burn`, `new_used = burnt + promises + use`, and the same clamp and variant rule.
The success condition is `new_burnt ≤ 10^15 ∧ new_used ≤ prepaid`. Success lowers `limit` when
`use > burn`. Arithmetic overflow gives `IntegerOverflow`.

**D13. Charge points (§2): no defect found.** The prose rules reproduce nearcore exactly on every family,
including:
* promise-window out-of-gas amounts;
* loops whose body starts with a bulk operator;
* nested targeted loops, `else`/`end` after dead code, and dead branches marking targets;
* `br_if`/`br_table` to the function label;
* the `GasLimitExceeded` window near 10^15.

Three points could be stated more explicitly:
1. For a targeted loop whose body starts with a bulk operator, this implementation merges the loop's `R`
   into the bulk point as `(R+B, U)`. Merged and separate points give identical outcomes in every probe.
2. The prologue charge is a separate point, ahead of the body's first point.
3. A live `end` of an *untargeted* block that follows a dead region starts a range that continues past
   the `end`.

**D14. Small §3/§5 clarifications.**
* The operand-stack simulation does not pop a dead `if`'s condition. The function's final `end` pushes the
  results, so the maximum is at least the result size even when the body ends in dead code.
* Zero-length segments at `offset == size` are fine, and `offset > size` traps. This is standard 2.0
  behaviour, but worth stating, since "out-of-bounds segment" is ambiguous.
* `memory.grow`/`table.grow` failures return −1 after paying the linear fee for the requested count.

## Files

* `nearwasm.py`: the implementation and CLI.
* `difftest_cr.py`, `run_all.sh`: the difftest drivers against the nearcore harness.
* `probes/`: the black-box probes behind the resolutions above. `probe.py` is the helper, `cmp()` runs both
  implementations, `origdiff.py` locates mutation sites, and `sizefit.py` collects prepared-module lengths.
