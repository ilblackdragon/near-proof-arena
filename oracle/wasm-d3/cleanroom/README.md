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

The host-function extension (checkpoint 3) additionally used: `docs/research/near-wasm-boundary-inventory.json`
(signatures, fees, compute overrides), `core/parameters` (the transfer and gas-key fee formulas in `cost.rs`),
the harness I/O code `src/main.rs` (`full` mode, context options, `fmt_action`), the generators
`tests/host_*.py`, the public SHA-256/Keccak/RIPEMD-160/RFC 8032 specifications, and
`oracle/tools/v3lib/ed25519.py` (dalek verify semantics) with the vectors in `oracle/fixtures/v3/ed25519/`.
It did not read `logic.rs`, `vmstate.rs`, `gas_counter.rs`, `logic/mocks/` or `wasmtime_runner/`. Every
order of charges and checks not stated in Appendix A was settled by black-box runs (`probes/host/`).

```
nearwasm.py [--charge-points | --full] [--trace] < cases   # `<prepaid> <wasm_hex> [<receivers> | k=v;...]`
difftest_cr.py (opcodes | random N SEED | promise N SEED | mutate N SEED | host N SEED | edges)
               [--shards K] [--timeout S] [--full]
run_all.sh                                  # the nine required families
nearwasm.py --chunk CODEHEX_FILE < trace    # checkpoint 3b: trie-backed chunk replay (see below)
difftest_ttn_cr.py TRACE [--shards K]       # checkpoint 3b: difftest against nearcore op-level traces
```

`host` and `edges` always compare in harness `full` mode; `--full` forces it for the other families.

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
* **Host functions:** all 89 PV86 `env` imports. The 14 curve functions (`alt_bn128_*`, `bls12381_*`,
  `ecrecover`, `p256_verify`) link, and calling one prints `out-of-domain`. The other 75 are implemented
  (see "Host functions" below).

## Host functions (checkpoint 3)

Added to `nearwasm.py` (plus `nearcrypto.py`, standard library only):

* **Gas profile and compute usage.** Every ExtCost charge records the gas it actually burnt (the clamped
  delta on failure). Action fees record their burnt part as action gas and as send-action compute. The
  output is `compute = Σ_k ⌊gas_k·compute_k/gas_k⌋ + send_compute + (burnt − action_gas − host_gas)`, using the
  compute overrides of the storage costs from the inventory.
* **Registers** (limits 100 registers, 100 MiB per register, 1 GiB in total, all `MemoryAccessViolation`),
  guest memory reads and writes, `get_memory_or_register`, UTF-8 and UTF-16 decoding (explicit length or
  NUL scan) with the log-length limits, and logs.
* **Context** from the harness: `alice.near`, signer and predecessor `bob.near`, `signer_account_pk = 000102`,
  block 10, timestamp 42, epoch 1, storage usage 1000, `chain_id = "test"`, zero random seed, zero
  validator stakes, and options `input`, `results`, `deposit`, `balance` and `rcv`.
* **Hashes and signatures:** SHA-256, Keccak-256/512, RIPEMD-160, and Ed25519 with ed25519-dalek 2.x `verify`
  semantics.
* **MockedExternal storage:** an in-memory map with no trie-node charges, and `storage_usage` accounting
  (+k+v+40 for a new record, ±Δv when overwriting, −(k+v+40) on remove).
* **Promises and receipts:** a receipt's index, and an action's index, is its position in the action log.
  Joint promises (`promise_and`) are flattened. Every batch action, including the implicit-account transfer
  surcharges and the gas-key fees, is rendered as the harness's `fmt_action` text (`OTHER` for global
  contracts, state init and gas keys). Data ids are `sha256(u64_le(counter))`.
* **Yield and resume,** with and without ids.
* **Promise results** from the context, `promise_return` (`receipt<i>`), and the VMOutcome balance
  (`balance + deposit − deductions`, with the one-yocto exemption).
* **Outcome assembly:** logs, actions and storage are reported on abort too, and the 0-gas nop outcomes
  print a zero `full` suffix.

### Host functions: ambiguities in Appendix A, and how black-box runs resolved them

Each item below is either a defect in Appendix A or prose §5–§7, or an order or value it leaves unstated.
"Mock" marks behaviour that may belong to the harness's `MockedExternal` rather than to production
`External`.

**H1. Storage eviction is free (Mock?).** Appendix A charges `storage_write_evicted_byte × old_len` on
overwrite and `storage_remove_ret_value_byte × old_len` on remove. Neither is charged. The old value is
still written to the register with WR(len). `storage_read` *does* charge `storage_read_value_byte × len`, and
for `len > 4000` also `storage_large_read_overhead_base + _byte × len`, whose compute is 41e9 + 3,111,005·len
although its gas is 1 + len.

**H2. Storage order.** Each storage function charges `base`, then its own `*_base`, then GMR(key), then checks
`KeyLengthExceeded` (on the key's actual length, register path included), then the per-byte charges.
`storage_write` reads the value and checks `ValueLengthExceeded` before both byte charges.

**H3. Action and receipt indices are positions in the action log (Mock).**
* `promise_batch_action_state_init*` returns that position.
* `set_state_init_data_entry`'s `action_index` must name a state-init action of the same receipt;
  otherwise it raises `InvalidActionIndex { receipt_index, action_index }`.
* `set_state_init_data_entry` resolves the promise index *before* reading the key and value (Appendix A
  lists `base; GMR(k); GMR(v)`). It then charges `deterministic_state_init_entry` (send 0) and `_byte × (k+v)`,
  then checks `InvalidActionIndex` and `DataEntryAlreadyExists`.
* Data entries do not appear in the action log.

**H4. `abort`.** The order is:
1. `base`.
2. Either pointer `< 4` → `BadUTF16`.
3. `NumberOfLogsExceeded`, before any read.
4. Read *both* u32 length prefixes (2×RM(4)), then decode the message, then the file name.

`log_byte` is charged on the message *without* the `"ABORT: "` prefix. The total-length limit counts the
prefixed log. The panic text is `{msg}, filename: "{file}" line: {l} col: {c}`.

**H5. Log-length failures at push time report the length twice.** If `total + L > 16384` for the log being
recorded (possible for `abort`, and for `log_utf16` when UTF-8 is longer than UTF-16, for example `€`), the
error is `TotalLogLengthExceeded { length: total + 2L }`. Gas (`log_base + log_byte·len`) has already been
charged.

**H6. UTF-16 and UTF-8 decoding are asymmetric.**
* **UTF-8, explicit length:** `utf8_decoding_base`, then `len > 16384 − total` → `TotalLogLengthExceeded {
  total+len }` *before* any memory read, then RM(len), then `utf8_decoding_byte × len`, then `BadUTF8`.
* **UTF-16, explicit length:** `utf16_decoding_base`, then RM(len) *first* (so `len = 2^63` gives
  `IntegerOverflow`, and a 2^31 `abort` prefix gives `GasLimitExceeded`), then the length check
  (`total+len`), then odd length → `BadUTF16`, then `utf16_decoding_byte × len`, then decoding.
* **NUL scans:** each UTF-8 byte costs `read_memory_base + read_memory_byte`, and each UTF-16 unit costs
  `read_memory_base + 2·read_memory_byte`.
  * UTF-8 fails at `total + max + 1` once more than `max = 16384 − total` bytes precede the NUL.
  * UTF-16 fails as soon as the bytes read *including the current unit* exceed `max`. It reports
    `total + that count`, which is `16386` from empty and `total + max + 1` for an odd `max`.
* `panic_utf8` is subject to the same log-length limit.
* *Note (source review, 2026-10-06): the UTF-16 explicit-length order above is refuted. nearcore checks odd
  length (`BadUTF16`) **before** the log-length check (`W:logic.rs:474-475`). Probe: `log_utf16(16385, 0)` →
  nearcore `BadUTF16`, nearwasm.py `TotalLogLengthExceeded{16385}`. See prose spec §7.2.*

**H7. Account-id decoding charges `utf8_decoding_byte` on the bytes actually read.** With the register path
(`len = u64::MAX`), charging the raw `len` (Appendix A's `AID(n)`) would overflow. Nearcore charges the
register's length.

**H8. Public keys are decoded after the promise lookup and the action fees.** This holds for `stake`,
`add_key_*`, `delete_key` and all gas-key functions; Appendix A says it only for `transfer_to_gas_key`.
* An undecodable key counts as length 0 in the gas-key per-byte fees.
* The accepted borsh forms are `00‖32`, `01‖64` (no curve check) and **`02‖1952` (ML-DSA-65)**. Appendix A
  says ML-DSA is rejected, but at PV86 the harness accepts it.
* In `transfer_to_gas_key`, `BalanceExceeded` comes *before* `InvalidPublicKey`.
* `num_nonces > u16` → `IntegerOverflow` right after GMR(pk), before the promise lookup.

**H9. Gas-key fee geometry**, which `cost.rs` leaves to `core/primitives`. It was fitted and then checked
for named and implicit receivers and for 33- and 65-byte keys:
* `GasKeyInfo` borsh length = 18 (send side of `add_gas_key_*`);
* minimum gas-key access-key value length = 27 (exec side of `transfer_to_gas_key`);
* access-key trie key = `1 + len(receiver) + 1 + len(pk)`;
* a nonce key adds `2`, and a nonce value is `8`.

**H10. Implicit-account transfer surcharges are one fee.** `transfer` (+`create_account` for NEAR-implicit,
ETH-implicit `0x…` and deterministic `0s…` receivers, +`add_full_access_key` for 64-hex NEAR-implicit) is
deducted in a single `deduct_gas`. This is observable in the clamp of a failing transfer.

**H11. Method-name lists** (`add_*key_with_function_call`) are split on `,` as bytes, and an empty name →
`EmptyMethodName`, before the promise lookup. Non-UTF-8 names are *accepted* (Mock). Appendix A cites
`InvalidMethodName` from the production receipt manager, which `MockedExternal` does not reproduce. The fee
is `Σ(len+1)`.

**H12. `promise_yield_create` order** (Appendix A omits when the receipt exists):
`base; yield_create_base; GMR(m); EmptyMethodName; GMR(a); yield_create_byte×(m+a); prepay(gas); RCPT(sir,
[sir]); create the yield receipt (YC logged); push the promise (NumberPromisesExceeded); ACT(function_call);
ACT(function_call_byte); append the FunctionCall; WR(32, data_id)`. `gas = u64::MAX` → `IntegerOverflow`
with no receipt.

**H13. `promise_yield_create_with_id` order differs from `promise_yield_create`:**
1. `base; yield_create_with_id_base` (*no* `yield_create_base`).
2. RM(16) amount.
3. GMR(m); `EmptyMethodName`.
4. GMR(a); GMR(yield_id); `YieldIdMalformed`. This comes *before* `yield_create_byte`.
5. `yield_create_byte`.
6. If the id is pending, return `u64::MAX` with no further charges and no balance check.
7. Otherwise **create the receipt first** (YC logged, even if a later prepay fails).
8. Prepay; RCPT; push; ACT ×2; `deduct_balance` (with the one-yocto exemption); append the FunctionCall.

**H14. Resume (Mock).**
* `promise_yield_resume` logs `YR:<data_id>:<payload>` for *any* 32-byte id, and returns 1 only for a
  created yield.
* `promise_yield_resume_with_yield_id` with an unknown id returns 0 and logs nothing.
* Data ids come from one counter, `sha256(u64_le(n))`, which only yield creation advances. Receipt data
  dependencies do not.

**H15. Receipts exist before the promise-count check.** `promise_batch_create`/`_then` log `CR(...)` (and
pay RCPT) before `NumberPromisesExceeded`. `promise_and` flattens joint promises, keeping duplicates, and
checks the 128-dependency limit on the flattened list.

**H16. `ed25519_verify` order.**
1. `ed25519_verify_base`.
2. GMR(sig); `len ≠ 64` → `Ed25519VerifyInvalidInput { msg: "invalid signature length" }`.
3. `sig[63] & 0xE0 ≠ 0` → return 0 (before reading the message).
4. GMR(msg); `ed25519_verify_byte × len`.
5. GMR(pk); `len ≠ 32` → `"invalid public key length"`.

`base` is not charged, and neither are the hash functions' `base` costs (as Appendix A's rows say).

**H17. Smaller confirmations.**
* `storage_iter_*` charge nothing, not even `base`.
* `current_contract_code` returns 0 without writing a register.
* `input` and `promise_result` charge `write_register_base` only.
* The 101st register write (or any write when 100 exist, including replacing one) → `MemoryAccessViolation`.
* `value_return` after `promise_return` replaces the return value.
* Panic messages use Rust `{:?}` escaping (`\0`, `\u{1}`, `\u{200b}`).
* Logs, the action log and storage survive an abort in the harness output.

**H18. Prose §4 sync after a failed action fee.** After `deduct_gas` fails, `burnt` can exceed the lowered
`limit`. The "sync once more on return" must therefore not burn when the wasm-side counter is unchanged.
A literal `burn(0)` would raise a second error and mask `GasLimitExceeded`.

## Agreement with nearcore (final run)

Checkpoint 3 (host functions, harness `full` mode: compute, logs, action log and storage compared):

| family | cases | compared | out-of-domain | unmodeled | skipped | disagreements |
|---|---|---|---|---|---|---|
| host 4000 seed 1 | 4,000 | 4,000 | 0 | 0 | 0 | **0** |
| host 4000 seed 2 | 4,000 | 4,000 | 0 | 0 | 0 | **0** |
| host 4000 seed 3 | 4,000 | 4,000 | 0 | 0 | 0 | **0** |
| host_edges | 442 | 442 | 0 | 0 | 0 | **0** |

Extra checkpoint-3 runs, all with 0 disagreements:
* host 4000, seeds 4–12;
* every earlier family re-run in `full` mode (`--full`): opcodes, random seeds 1 and 2, promise seeds 1 and 2,
  mutate seed 11;
* all 7,265 Ed25519 fixture vectors through `ed25519_verify` (`probes/host/p14.py`, 3,543 valid);
* the probe files `probes/host/p1.py` … `p14.py`. `p12.py` perturbs every argument of every non-curve host
  function, one at a time, alone and together with an invalid promise index: 501 cases.

Regression of the checkpoint-2 families (default mode), unchanged:

| family | cases | compared | out-of-domain | unmodeled | skipped (>20 s) | disagreements |
|---|---|---|---|---|---|---|
| opcodes (`opcases.py`) | 9,175 | 9,174 | 1 (`float-local`) | 0 | 0 | **0** |
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

## Storage cost model (checkpoint 3b)

`nearstore.py` (standard library only) adds the trie-backed contract storage with trie-node ("TTN")
accounting. Its only normative source was `docs/research/d3-trie-accounting.md` §4 (prose, 4.1–4.4) and
§5 (trace format), plus Appendix A of `near-wasm-boundary.md` for the cost values. It did not use the Lean
modules (`TrieStore`, `TrieAccounting`, `ChunkStorage`, `Host`), `oracle/wasm-d3/lean`, `oracle/d3-ttn/src`
or any nearcore source. From `oracle/d3-ttn` only the I/O format of `difftest_ttn.py`, the contract
`ttn.wat`/`ttn.wasm` and the `near-d3-ttn` binary (run as a black box to make traces) were used.

* **Backends.** The storage host functions now call a store: `MockStore` (the harness's MockedExternal,
  unchanged behaviour) or `TrieStore`, one per call, over a `Chunk` holding the pre-state (root plus recorded
  nodes and values keyed by SHA-256), the committed overlay, and the chunk-scoped accounting cache.
* **`nearwasm.py --chunk CODEHEX_FILE`** reads §5 trace lines on stdin, ignores the expected columns, and
  runs each call as method `run` of the contract with `input = args`, `prepaid`, and current account =
  `account` (other context as the harness defaults). It prints one line per call:
  `<ok|fail> <wasm_gas> <ext_gas_total> <s0> … <s10>`, slots in the §5 order. `wasm_gas = burnt − Σ ext`
  (no actions here). A call's overlay changes are committed iff it is `ok`.
* **`difftest_ttn_cr.py TRACE [--shards K]`** shards the chunk lines over K processes and compares every
  call line with the trace's 14 expected columns.
* **`NEARSTORE_ABLATE=<rule,...>`** switches on deliberately wrong variants, one per prose rule, to show the
  comparison is sensitive to each (table below).

### Agreement with nearcore

Traces from `near-d3-ttn --seed S --blocks 60` (4 shards, nearcore outcome profiles):

| trace | chunks | calls | failed calls | calls with TTN/cached charges | disagreements |
|---|---|---|---|---|---|
| seed 101, `--ops 300` | 236 | 704 | 59 | 673 | **0** |
| seed 102, `--ops 300` | 236 | 774 | 58 | 732 | **0** |
| seed 103, `--ops 300` | 236 | 754 | 56 | 704 | **0** |
| seed 104, `--ops 300` | 236 | 686 | 62 | 651 | **0** |
| seed 105, `--ops 300` | 236 | 694 | 57 | 655 | **0** |
| seed 106, `--ops 300` | 236 | 704 | 62 | 663 | **0** |
| seed 101, `--ops 40`  | 236 | 630 | 0  | 605 | **0** |

Total: 4,946 calls, 0 disagreements. All 354 failed calls are gas exhaustion (`wasm + ext = prepaid`),
several of them inside a storage charge, so clamped partial charges are compared too. Every slot is nonzero
in most calls, including the large-read slots and `BranchWithValue` nodes (the 2-byte key `k‖x` is a prefix
of the 3-byte key `k‖x‖0x55`).

Sensitivity: each ablation breaks agreement (the `--ops 40` trace has no failed calls, so the two
failure-only rules were checked on seed 101 `--ops 300`).

| `NEARSTORE_ABLATE` | rule it breaks | disagreements |
|---|---|---|
| `fresh-cache` | cache is chunk-scoped (4.1) | 401 / 630 |
| `no-overlay` | committed writes persist across receipts (4.4) | 314 / 630 |
| `read-touch-path` | a trie read touches no node (4.3) | 589 / 630 |
| `no-read-warm` | a read's value dereference warms the cache (4.4 subtlety 2) | 197 / 630 |
| `no-value-touch` | write/remove touch the old value's hash (4.3 step 2) | 567 / 630 |
| `no-absent-remove` | a remove records `removed` even when absent (4.3 step 3) | 202 / 630 |
| `keep-failed` | a failed receipt's writes are rolled back (4.4) | 83 / 704 |
| `ttn-before-bytes` | evicted/removed bytes are charged before the node commit (4.3 step 2) | 3 / 704 |

### Findings: where §4/§5 was silent or ambiguous, and what black-box runs showed

**T1. The contract-loading fee is an ext cost.** §5 says the ext total "includes the evicted/removed-byte
charges and every other host cost", and Appendix A describes the loading fee only as a gas charge after
loading. The first replay had every call off by exactly `+723,880,403` in wasm gas and the same amount
fewer in ext gas, which is `contract_loading_bytes × 632 + contract_loading_base` for the 632-byte
`ttn.wasm`. nearcore profiles the loading fee under the ext costs `contract_loading_bytes` and
`contract_loading_base`, so the wasm column is `burnt − ext` with the loading fee counted as ext. The
clean-room now records it under those two keys. The old harness output does not change, because their gas
and compute values are equal.

**T2. Order of the evicted/removed-bytes charge and the node commit.** §4.3 step 2 lists the touches, then
the `B × length` charge, the value touch, and the commit. It does not say plainly that the commit's TTN and
CACHED charges come **after** `B`. That only matters when gas runs out. Charging the commit first gives 3
disagreements on seed 101 (calls that run out inside these charges, where the clamped split between the
`storage_*_evicted/ret_value_byte` and TTN entries differs). The prose order (B first, the commit last) is
correct.

**T3. Whether the old value's hash is touched by write/remove.** The prose says so ("touch the value hash
and fetch the value"), but §1/§2 only talk of trie *nodes*. Black-box: the value hash is touched and
charged as a node (567/630 disagreements without it).

**T4. The failure mode of the commit.** "Charge `TTN × Δdb`, then `CACHED × Δmem`; each is a `pay_per`"
leaves open what happens when the first one fails. Following Appendix A's `pay_per` (clamped burn, then
stop, so CACHED is never charged) agrees on all 354 failed calls.

**T5. A read's commit.** §4.3 says that for `storage_read` "the commit happens but charges 0". The
`touching_trie_node`/`read_cached_trie_node` entries are therefore 0-gas `pay_per` calls. This is
unobservable in the gas and slot columns, and the clean-room records them as 0. Touching the path on a read
is clearly wrong (589/630).

**T6. Value charges on a trie read use the value-ref length.** §4.3 says the read's "same value charges as
in step 1" are applied "if present", before the value hash is touched and the value fetched. The length
therefore comes from the value ref `(length, hash)`, before the fetch. The large-read threshold (`len >
4000`) is strict, and the 4,500-byte values of `ttn.wat` hit it. The large-read profile slots are recorded
at 1 gas per unit, as in Appendix A (`storage_large_read_overhead_{base,byte}` have gas 1), so the slots
count reads and bytes.

**T7. `has_key` against an overlay `removed`.** "Overlay first" does not say what `removed` gives: it gives
absent, and nothing is charged or touched in either case.

**T8. Unstated context.** §5 gives only `account`, `prepaid` and `args`. The other context (signer,
predecessor, balance, block) does not affect `ttn.wasm`. `max_gas_burnt` (the harness's 10^15 vs
mainnet's 300 Tgas) is never reached, because `prepaid ≤ 300 Tgas` in every trace, and both errors fail the
call anyway. The traces showed no failure other than gas exhaustion: no `LackBalanceForState`, and no
storage error. A storage error (missing node or value) would make the replay print `unmodeled storage
error`.

**T9. Node decoding details** were not needed beyond the prose. The trailing 8-byte `memory_usage` follows
the body. Hex-prefix bit 1 marks a leaf key (it is never checked against the tag), and a nonzero padding
nibble on even keys is rejected. Leaf presence is exact nibble equality. Values are fetched by hash from the
same recorded-storage map as the nodes.

## Files

* `nearwasm.py`: the implementation and CLI.
* `nearstore.py`: the storage backends (MockedExternal map, and the trie-backed chunk store with TTN
  accounting, checkpoint 3b).
* `difftest_ttn_cr.py`: the checkpoint-3b difftest against `near-d3-ttn --trace` files.
* `nearcrypto.py`: Keccak, RIPEMD-160 and Ed25519 (dalek `verify`) for the host functions.
* `probes/host/`: the host-function black-box probes (`hp.py` is the helper; `cmp()` runs both
  implementations in `full` mode).
* `difftest_cr.py`, `run_all.sh`: the difftest drivers against the nearcore harness.
* `probes/`: the black-box probes behind the resolutions above. `probe.py` is the helper, `cmp()` runs both
  implementations, `origdiff.py` locates mutation sites, and `sizefit.py` collects prepared-module lengths.
