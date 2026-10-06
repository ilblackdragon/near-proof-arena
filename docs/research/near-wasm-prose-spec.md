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
* **Sync** means: `d := max(0, (prepaid − burnt − promises) − g)` (both subtractions saturating at 0), and
  burn `d` **only if `d > 0`**. After a failed action fee (`deduct_gas`), `burnt` can exceed the lowered
  `limit`; a literal `burn(0)` would then fail a second time and could mask the first error (e.g.
  `GasLimitExceeded`).
  (Errata H18, §7.2.)
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


## 7. Errata from the clean-room implementation (2026-10-06)

A clean-room implementation written from this document (`oracle/wasm-d3/cleanroom/`) agrees with nearcore
and with the Lean spec on every test family. Where this document was silent or wrong, it settled the question
by black-box runs against nearcore. Its README (§ "Defects and gaps", D1–D14) is the authoritative errata
list. In summary:
* **D1:** linking and the outcome order: loading fee → link → method resolution → instantiation → start → `main`.
* **D2:** only single-byte block types.
* **D3/D9:** count and section-validation order.
* **D4:** `TooManyLocals` is checked while parsing, with a permissive local-type parse.
* **D5:** no table parser limit below u32.
* **D6:** `Serialization` for renamed export names over 100,000 bytes.
* **D7:** the instrumented size is not derivable from this document. The Lean `InstrSize` model is exact.
* **D8:** encoding deviations from WebAssembly 2.0: LEB indices for bulk memory and tables, but a single
  zero byte for `memory.size`/`memory.grow` and the `call_indirect` table index.
* **D10–D12:** per-function and host-function check order, and `deduct_gas` failures.
* **D13:** charge points are correct as stated. One position ambiguity remains: a point at the `end` that
  closes a dead region may equivalently be placed after it. Both placements give identical outcomes.
* **D14:** operand-stack and segment clarifications.

### 7.2 Errata from the clean-room host-function extension (H1–H18)

Checkpoint 3 of the clean-room implementation added the 75 non-curve host functions, written from
§5 and `near-wasm-boundary.md` Appendix A and settled by black-box runs against the D3 harness. Its
README lists H1–H18. Each was checked against the pinned nearcore 2.13.4 source and classified:
**(a)** Appendix A or this document was wrong or silent for production nearcore, corrected in place;
**(b)** the black-box result is specific to the harness's `MockedExternal`, and Appendix A now states both
behaviours; **(c)** not confirmed by source, not applied. Citations: "W:" =
`runtime/near-vm-runner/src/wasmtime_runner/`, "L:" = `runtime/near-vm-runner/src/logic/`, `ext.rs` =
`runtime/runtime/src/ext.rs`, `mock_external.rs` = `L:mocks/mock_external.rs`. Production `External`
trie charges are specified authoritatively by `docs/research/d3-trie-accounting.md` §4.3.

| # | Class | Correction (Appendix A row or section) | Source |
|---|---|---|---|
| H1 | b | `storage_write_evicted_byte×old_len` and `storage_remove_ret_value_byte×old_len` are charged by production `RuntimeExt` (through `deref_write_evicted_value_bytes` / `deref_removed_value_bytes`, *before* the value deref and the TTN commit), not by `W:logic.rs`; `MockedExternal` charges neither, so eviction is free under the harness while WR(old_len) is still paid. `storage_read`'s value and large-read charges are in `W:logic.rs` and apply under both. Rows storage_write/read/remove. | `W:logic.rs:4508, 4668`; `ext.rs:166-174, 250-261`; `L:gas_counter.rs:408-413`; `mock_external.rs:171-199` |
| H2 | a | Storage order: `base`, PIV, `*_base`, GMR(k), `KeyLengthExceeded` on the key's actual length (register path included), then (write) GMR(v), `ValueLengthExceeded`, then the per-byte charges. | `W:logic.rs:4473-4507, 4573-4587, 4646-4667` |
| H3 | a + b | (a) `set_state_init_data_entry` resolves the promise index *before* GMR(k)/GMR(v); `deterministic_state_init_entry` has send fee 0; `InvalidActionIndex`/`DataEntryAlreadyExists` come after both fees. (b) Action and receipt indices: production = index within the receipt's actions / in `action_receipts`; mock = position in one global action log. Data entries live inside the state-init action. | `W:logic.rs:2885`; `parameters.yaml:128-132`; `receipt_manager.rs:87-98, 322-347`; `mock_external.rs:344-386` |
| H4 | a | `abort`: `base`; pointer < 4 → `BadUTF16`; `NumberOfLogsExceeded` before any read; both RM(4) length prefixes; UTF16(msg); UTF16(file). `log_byte` on the message without `"ABORT: "`; the limit counts the prefixed log; panic text `{msg}, filename: "{file}" line: {l} col: {c}`. | `W:logic.rs:4316-4345` |
| H5 | a | A log-length overflow detected at push time reports `TotalLogLengthExceeded{total+2L}` (the total is incremented before the error is built); `log_base + log_byte×len` is already charged. | `L:logic.rs:105-124` |
| H6 | a, partly c | UTF-8 explicit: base; `n > max` → `{total+n}` before any read; RM(n); byte charge; `BadUTF8`. NUL scans as in the README. **UTF-16 explicit order corrected from source, not from the README:** base; RM(n); odd `n` → `BadUTF16`; *then* `n > max` → `{total+n}`; byte charge; decode. The README (and `cleanroom/nearwasm.py`) put the length check before the odd check; nearcore checks odd length first. A black-box probe confirms nearcore: `log_utf16(16385, 0)` → `BadUTF16`, where the clean-room gives `TotalLogLengthExceeded{16385}` (same gas). The rest of H6 is confirmed. Notation rows UTF8/UTF16. | `W:logic.rs:392-427, 454-507` (odd check at 474, length check at 475) |
| H7 | a | `AID` charges `utf8_decoding_byte` on the bytes actually read (the register's length in register mode), not on the raw `len`. | `W:logic.rs:4424-4426` |
| H8 | a | Public keys are decoded after the promise lookup and the action fees in stake, add_key*, delete_key and all gas-key functions; an undecodable key counts as length 0 in the gas-key fees; `transfer_to_gas_key` raises `BalanceExceeded` before `InvalidPublicKey`; `num_nonces > u16` → IntegerOverflow right after GMR(pk). ML-DSA-65 (`02‖1952`) is **accepted** at PV86 in production too: `PostQuantumSignatures` is a PV85 feature. | `W:logic.rs:3188-3212, 3258, 3426, 3477, 3570, 3625`; `L:logic.rs:236-258`; `core/primitives-core/src/version.rs:567`; `ext.rs:620-622` |
| H9 | a | Gas-key fee geometry: `GasKeyInfo` borsh length 18; minimum gas-key `AccessKey` borsh length 27; access-key trie key `1 + len(receiver) + 1 + pk_len`; a nonce key adds 2 (u16) and a nonce value is 8 (u64). `pk_len` includes the tag byte. The exec side uses the receipt's receiver. | `core/parameters/src/cost.rs:794-880`; `core/primitives-core/src/trie_key.rs:13-15`; `core/primitives-core/src/account.rs:481-487, 556-558` |
| H10 | a | `transfer` plus its implicit-account surcharges is one `pay_action_accumulated` (one `deduct_gas`). | `W:logic.rs:3123-3142`; `core/parameters/src/cost.rs:722-776` |
| H11 | a + b | (a) Method-name lists are split on byte `,`, an empty name → `EmptyMethodName` before the promise lookup, and the fee is Σ(len+1). (b) Non-UTF-8 names: production raises `InvalidMethodName` when the action is appended (after the fees); `MockedExternal` accepts them. The same split applies to function_call's method name. | `L:utils.rs:4-20`; `W:logic.rs:3549`; `receipt_manager.rs:382, 500, 598`; `mock_external.rs:388-406, 472-490` |
| H12 | a | `promise_yield_create` order, including RCPT and receipt creation before `NumberPromisesExceeded`, and IntegerOverflow for `gas = u64::MAX` in the prepay, before any receipt. | `W:logic.rs:3731-3802`; `L:gas_counter.rs:118-142` |
| H13 | a | `promise_yield_create_with_id` order: no `yield_create_base`; RM(16) amount before the method name; `YieldIdMalformed` before `yield_create_byte`; pending → `u64::MAX` with no further charges and no balance check; the receipt is created *before* the prepay; `deduct_balance` after both ACTs. "Pending" = trie mapping in production, action-log entry in the mock. | `W:logic.rs:3805-3920`; `ext.rs:371-400`; `mock_external.rs:256-277` |
| H14 | b | Resume and data ids are mock behaviour. Mock: logs `YR` for any 32-byte id, returns 1 only for a yield created in the call, and data ids = `sha256(u64_le(n))` advanced only by yield creation. Production: returns 1 iff a yield receipt or status exists in state, and data ids = `create_receipt_id_from_action_hash(action_hash, block_height, n)`, with `n` also advanced by every data dependency of `create_action_receipt`. | `mock_external.rs:205-211, 236-317`; `ext.rs:303-311, 342-351, 402-440` |
| H15 | a | `promise_batch_create`/`_then` pay RCPT and create the receipt before `checked_push_promise`'s `NumberPromisesExceeded`. `promise_and` flattens joint promises, keeping duplicates, and checks 128 on the flattened list. | `W:logic.rs:2176-2201, 2244-2247, 2308-2311, 516-528` |
| H16 | a | `ed25519_verify`: `ed25519_verify_base` (no `base`); GMR(sig); length → `"invalid signature length"`; `sig[63]&0xE0≠0` → 0 *before* the message is read; GMR(msg); byte charge; GMR(pk); length → `"invalid public key length"`. Hash functions charge their own `*_base`, not `base` (as the rows already said). | `W:logic.rs:1783-1851, 1499-1514` |
| H17 | a + b | (a) Confirmed and made explicit: `storage_iter_*` charge nothing, not even `base`; `current_contract_code` returns 0 without writing a register; `input`/`promise_result` charge `write_register_base` only; any register write while 100 registers exist (including a replacement) → `MemoryAccessViolation`; `value_return` after `promise_return` replaces the return data; an aborted outcome keeps its logs. (b) Harness output only: `{:?}`-escaped panic text (production uses `Display`, "Smart contract panicked: {msg}"), and printing the action log and storage after an abort (production discards an aborted call's receipts and state changes). | `W:logic.rs:4768-4847, 4366-4369, 4148, 4219`; `L:vmstate.rs:229-262`; `L:logic.rs:4498-4502`; `L:errors.rs:540` |
| H18 | a | §4 sync burns only a positive difference (saturating). Corrected in §4 and in Appendix A §3. | `W:mod.rs:1049-1061`; `L:gas_counter.rs:147-166, 389-391` |

Refuted part: only the UTF-16 explicit-length check order in H6 (class c). The clean-room passes its
difftests because no generated case has an odd length above the remaining log budget. Its `get_utf16`
should check odd length before the log length.
