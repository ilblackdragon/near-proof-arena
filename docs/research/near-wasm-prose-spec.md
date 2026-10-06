# NEAR WASM execution at PV86: prose specification for clean-room implementations

Purpose: requirements v0.2 §2.2 and review F5/C9. This document is written so that a second author can
implement NEAR's contract-execution semantics **without reading nearcore's instrumentation, finite-wasm, or
our Lean spec**, and then be difftested against both. It states *what* happens. Where nearcore's behaviour
is an artefact of its implementation (a "quirk"), the quirk is stated explicitly. Scope is the D3α subset
covered by checkpoint 2: integer WASM plus `value_return`, `panic`, `gas`, `promise_batch_create`, and
`promise_batch_action_function_call`.

Numbers (PV86): `R = 822,756` (regular op cost), `B = 26,328,192` and `U = 822,756` (linear base and
unit), stack budget `S = 262,144`, `max_gas_burnt = 10^15`.

## 1. Preparation (accept/reject), in order

A contract is rejected with `CompilationError(PrepareError(<v>))` and **0 gas** at the first failing check,
in binary-section order:

1. **Parse and validate** with WebAssembly 2.0 rules. The enabled features are MVP, mutable globals,
   sign-extension, saturating float→int, reference types (funcref only: `externref` is invalid) and bulk
   memory. Multi-value, SIMD, threads, tail calls, memory64, multi-memory, exceptions, GC, function
   references and wide arithmetic are invalid. Implementation limits: ≤ 50,000 params+locals per function,
   names ≤ 100,000 bytes, ≤ 1,000 params per type, br_table ≤ 131,072 entries. Any violation →
   `Deserialization`.
2. **Section-specific checks**, evaluated when that section is reached:
   * type section with > 1,024 entries → `TooManyTypes` (checked before parsing the entries);
   * imports:
     * the module name must be `env`, else `Instantiate`;
     * table or global imports → `Instantiate`; memory import → `Memory`;
     * function imports count against the 10,000-function budget → `TooManyFunctions`;
   * table section: more than 1 table → `TooManyTables`; any table with an initial size > 10,000 →
     `TooManyTableElements`;
   * code section:
     * imports + bodies > 10,000 → `TooManyFunctions`;
     * a body larger than 196,608 bytes → `FunctionBodyTooLarge`;
     * the running total of declared locals > 1,000,000 → `TooManyLocals`.
3. **After parsing, per function in order:**
   * params > 64 → `TooManyParamsPerFunction`;
   * running total of params > 50,000 → `TooManyParamsPerContract`;
   * the function's maximum operand-stack bytes (§3) > 8,192 → `OperandStackTooLarge`;
   * `block`+`loop`+`if` count > 5,000 → `TooManyBlocksPerFunction`;
   * the running total > 50,000 → `TooManyBlocksPerContract`.
4. If the instrumented module would exceed 16 MiB → `InstrumentedCodeTooLarge`.
5. The module then fails to compile, as `WasmtimeCompileError` with 0 gas, if any function has
   params+locals > 49,998 (instrumentation adds 2 locals; the engine's limit is 50,000).

## 2. Gas charging (the "charge points")

Every operator has a **fee**:
* 0 for `block`, `else`, `end`;
* `B + U·n` for `memory.grow`, `memory.copy`, `memory.fill`, `memory.init`, `table.grow`, `table.copy`,
  `table.fill` and `table.init`, where `n` is the operator's last (top-of-stack) operand at run time;
* `R` for every other operator, including `loop`.

Gas is not charged operator by operator. It is charged at **charge points** placed before certain operators.
A point carries a constant `c` and a linear coefficient `l`. When execution reaches the point, it charges
`c + l·n` (with `n` the top operand of the following operator, for linear points) **before** that operator
runs. The points are a function of the body alone. They are built as follows.

**Operator classes.**
* **Plain:** constants, locals, globals, arithmetic, comparisons, conversions, `drop`, `select`, `nop`,
  `memory.size`, `table.size`, `ref.null`, `ref.func`, `ref.is_null`, `data.drop`, `elem.drop`, `block`,
  and integer ops other than div/rem.
* **Effect:** can trap, branch or call — all loads and stores, integer `div`/`rem` (signed and unsigned,
  both widths), `call`, `call_indirect`, `table.get`, `table.set`, `if`, `br`, `br_if`, `br_table`,
  `return`, `unreachable`.
* **Bulk:** the eight linear-fee operators.
* `loop` and `end`/`else` are special (below).

**Dead code.** After `br`, `br_table`, `return` or `unreachable`, the rest of the enclosing block (up to its
`end` or `else`) is dead, and so is everything nested inside it. No fee from dead code is ever charged, and
dead code gets no points. The block's own closing `end`/`else` is live again if the block's opening was live.
*Quirk:* branches inside dead code still count when deciding which blocks are branch targets.

**Branch targets.**
* A `block` or `loop` is *targeted* if any `br`/`br_if`/`br_table` (live or dead) names it.
* `if` blocks are always targeted. The `if` itself jumps to its `else` or `end`.
* `return` targets the function body.

**Ranges.** Split the live operators into ranges. A range is a run of operators in which, once the first
one runs, all the others run too (absent a trap in the last one). Concretely:

* The first operator of the body starts a range.
* An effect operator is always the **last** operator of its range, and a new range starts right after it.
* A bulk operator is alone in its range: a new range starts at it and another right after it.
* A new range starts **right after** every `end` that closes a targeted `block` or any `if`, and right after
  every `else`. Branches land after those operators. The `end`/`else` itself belongs to the preceding range,
  and its fee is 0.
* **Targeted `loop`:** a new range starts at the first operator of the loop body. That range also carries
  the `loop`'s own fee `R`, so `R` is paid on every iteration. The `loop` operator itself ends the preceding
  range.
* **Untargeted `loop`:** no boundary. The `loop` and its fee `R` simply belong to the surrounding range.
* A new range starts at the first live operator after a dead region (for example after the `end` of an
  inner block that became dead).
* `block`, and the `end` of an untargeted `block` or `loop`, are not boundaries.

Within a range, the point sits at the range's first operator and carries the sum of the fees of the range's
operators. A bulk range's point carries `(B, U)`. Points with total fee 0 are omitted.
*Equivalently:* each live operator's fee is paid at the start of the straight-line run that contains it,
where runs are broken at effects, bulk ops, branch targets and targeted loop headers.

**Function prologue.** On every function entry, before the body's first point, two things happen:
* **Stack:** `S_remaining -= op_stack_max + frame`, where:
  * `frame = 64 + Σ size(param and local)` with i32 = 4, i64 = 8, ref = 8;
  * `op_stack_max` is §3's static maximum.

  If `S_remaining` would go negative, execution stops with `HostError(MemoryAccessViolation)`. The
  charge is added back on every function exit.
* **Gas:** charge `⌈frame/8⌉·R`.

## 3. Operand-stack maximum (static, per function)

Simulate the operand stack in bytes along the body, in operator order (no branching), and take the maximum.
* Pushes: i32 = 4, i64 = 8, ref = 8.
* Inside dead code (§2), pushes and pops are ignored.
* At a block's `end`, reset the height to the block's entry height, then push the block's result.
* `else` resets to the `if`'s entry height.
* *Quirk:* `call_indirect` pops the callee's params and pushes its results, but does **not** pop its table
  index operand. The extra 4 bytes stay counted until the enclosing block ends.
* The other operators follow their WebAssembly types, popping first and then pushing (`select` pops 2 net).

## 4. The gas counter

State:
* `burnt`, `promises` (gas attached to promises), `prepaid`;
* `limit` = min(10^15, prepaid), lowered to `min(10^15, prepaid − promises)` whenever promise gas is
  attached;
* a wasm-side copy `g` of the remaining gas, `prepaid − burnt − promises`.

* **Charge point** with amount `a`. If `a ≤ g`, then `g -= a`. Otherwise:
  1. sync: burn `(prepaid − burnt − promises) − g`;
  2. try to burn `a`.

  The second step fails (it always does here; see below).
* **Burn `x`.** If `burnt + x ≤ limit`, add it. Otherwise fail:
  * set `burnt := min(burnt + x, min(prepaid, 10^15))`;
  * set `promises := min(prepaid, burnt_attempted + promises) − burnt`;
  * report `GasLimitExceeded` if `burnt + x > 10^15`, else `GasExceeded`.

  *Note:* the clamp is to `prepaid`, not to `limit`. With promises, `burnt` can therefore exceed `limit`.
  Because a charge point charges a whole range, the burnt amount depends on the range.
* **Host calls.** Sync before the call. After it returns, set `g := prepaid − burnt − promises`. On return
  from wasm to the host (normally or by a trap), sync once more.
* **Loading fee.** Before execution: `1,089,295 × code_len`, then `35,445,963`. Failure → `GasExceeded`
  with burnt clamped. A missing `main` export, or a `main` that is not `() → ()`, gives a 0-gas
  `MethodResolveError` (the loading fee is discarded).

## 5. Execution

* Standard WebAssembly 2.0 semantics.
* Memory is always 1,024 pages initially with a 2,048-page maximum, whatever the module declares;
  `memory.grow` beyond the maximum returns −1. Tables are capped at 10,000 elements.
* Instantiation: element segments, then data segments (an out-of-bounds segment is a
  `WasmTrap(MemoryOutOfBounds)` that keeps the loading fee). The start function then runs as its own entry,
  with the same gas rules.
* Trap names:

  | Cause | Trap |
  |---|---|
  | memory, table, or `call_indirect` index out of bounds | `MemoryOutOfBounds` |
  | div/rem by zero, signed overflow | `IllegalArithmetic` |
  | `unreachable` | `Unreachable` |
  | null table entry | `IndirectCallToNull` |
  | signature mismatch | `IncorrectCallIndirectSignature` |

Host functions, with their order of charges and checks, are defined by `docs/research/near-wasm-boundary.md`
Appendix A. The clean-room implementation may read that appendix: it describes behaviour, not code.

## 6. Outcome line (for the difftest)

* Success: `ok <burnt> <used> <return-hex or -> <balance>`.
* Failure: `abort <burnt> <used> <error>`, where `used = burnt + promises`.
