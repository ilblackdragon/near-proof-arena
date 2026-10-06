# D3 WASM boundary and implementation strategy

Date: 2026-10-06. Requirements: [D3 contract](../requirements/D3_WASM_REQUIREMENTS.md).
Baseline: nearproof `6fc8df7`; nearcore
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, PV86, mainnet parameters.

**Checkpoint 1: ready for lead review; implementation approval is pending.**
This document and its inventory are source research, not Lean definitions,
kernel proofs, executed WASM tests, or an admitted D3 candidate. Checkpoints
2–7 remain open. No requirement, challenge, claim encoding, or trusted
interface is changed by this work.

## 1. Reproducible boundary evidence

[near-wasm-boundary-inventory.json](near-wasm-boundary-inventory.json) records
207 parameters, 103 import declarations with signatures and availability,
WASM feature constants, and SHA-256 hashes of 54 pinned source files. The
generator reads Git objects at the exact nearcore commit, including its lockfile;
local modifications and a different checkout HEAD cannot alter the extraction.

Reproduce from the repository root (Python 3 and
[`tools/d3/requirements.txt`](../../tools/d3/requirements.txt)):

```sh
python3 tools/d3/boundary_inventory.py \
  --nearcore /data/illia/nearproof-deps/nearcore \
  --check docs/research/near-wasm-boundary-inventory.json
```

Use `--output` instead of `--check` to regenerate after an intentional review.
The tool rejects duplicate YAML keys, inconsistent old parameter values,
unparsed imports, unresolved host gates, and unknown host build-feature gates.
The parameter values are the YAML representation before nearcore's typed
conversion: monetary strings remain strings, and gas/compute records remain
records. This is **not** a substitute for exporting `RuntimeConfigStore` from
the oracle and comparing every typed field before implementing Lean costs.

Source paths below are relative to the pinned nearcore tree unless prefixed
`spec/`, `oracle/`, or `zk-formal/`. The inventory pins their content. The main
source entry points are
[`features.rs`](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/near-vm-runner/src/features.rs),
[`prepare_v3.rs`](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/near-vm-runner/src/prepare/prepare_v3.rs),
[`imports.rs`](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/near-vm-runner/src/imports.rs),
and [`function_call.rs`](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/runtime/src/function_call.rs).

## 2. VM and preparation boundary

**Wasmtime is confirmed.** `core/parameters/src/config_store.rs::CONFIG_DIFFS`
applies the mainnet base and registered diffs through 85 for a PV86 lookup;
there is no 86 parameter diff. `84.yaml` changes `NearVm` to `Wasmtime` and
enables `reftypes_bulk_memory`. `85.yaml` enables additional host APIs.
Do not apply the 129 or 155 diffs. `FixContractLoadingCost` is still disabled;
PV86 does enable `EnforcePerReceiptStorageProofLimit` in
`core/primitives-core/src/version.rs`.

`runtime/near-vm-runner/src/prepare.rs::prepare_contract` selects preparation
v3. Its feature validator, rather than Wasmtime's broader engine defaults,
defines the input language:

| Feature | Input boundary at PV86 |
|---|---|
| Core integer, f32/f64, mutable globals | enabled |
| Sign extension, saturating float-to-int | enabled |
| Reference types, bulk memory | enabled |
| Multi-value, SIMD, relaxed SIMD, threads | disabled |
| Tail calls, multi-memory, memory64 | disabled |
| Exceptions/legacy exceptions, GC/GC types, typed function references | disabled |
| Extended constants, memory control, custom page sizes | disabled |
| Component model and component async facilities, stack switching | disabled |
| Wide arithmetic | disabled for input modules |

The engine enables wide arithmetic separately; that does not override input
validation. Generated instrumentation and original code need distinct opcode
inventories. `wasmtime_runner/mod.rs::new_for_target` selects Winch on x86_64
and Cranelift elsewhere, enables NaN canonicalization, and sets a large native
stack ceiling so instrumentation enforces the protocol stack limit. Use
x86_64/Winch for the target oracle. Floating-point semantics must distinguish
arithmetic NaN production from bit-preserving loads, stores, constants,
reinterpretation, and sign operations; blanket canonicalization would be wrong.
The existing `NearSpecV3.F64` is limited to non-negative congestion arithmetic
and is not a WASM floating-point implementation.

Preparation is an observable staged computation:

1. Decode and validate using the feature set above. Apply type, function,
   local, table, function-body and other limits.
2. Permit original imports only from `env`, only of function type. Reject
   imported memories (including `env.memory`), tables, globals and tags with
   the source's distinct errors. Unknown function names and signature
   mismatches are not all rejected here: import linking occurs later.
3. Normalize memory to the configured initial/maximum sizes; insert memory
   when absent. Rewrite exports and start handling as `PrepareContext::run`
   does. Preserve the exact order of validation, normalization and failures.
4. Run finite-wasm-6 gas/stack analysis, then `InstrumentContext` with
   namespace `internal`. Original contracts cannot import that namespace.
   Preserve start-function execution and the generated export/global protocol.
5. Bound the instrumented output, compile, link, resolve an exported `() -> ()`
   method, instantiate and execute. Preparation, link, method-resolution and
   execution failures have different outcomes and gas paths; they are not a
   single `false` result.

`prepare.rs` has older descriptive comments about memory; the v3 code and
tests allow internal memory declarations and normalize them. Follow the code.

| Limit/cost | PV86 value |
|---|---:|
| Original contract / instrumented code bytes | 4,194,304 / 16,777,216 |
| Initial / maximum memory pages (64 KiB each) | 1,024 / 2,048 |
| Stack-height budget | 262,144 |
| Functions / locals per contract | 10,000 / 1,000,000 |
| Tables / elements per table | 1 / 10,000 |
| Function body bytes / types per contract | 196,608 / 1,024 |
| Blocks per function / contract | 5,000 / 50,000 |
| Parameters per function / contract | 64 / 50,000 |
| Operand-stack bytes per function | 8,192 |
| Regular operation cost | 822,756 |
| Linear operation base / unit | 26,328,192 / 822,756 |
| Max burnt / total prepaid gas | 1,000,000,000,000,000 each |

These limits act at different layers, not all in `prepare`. Stack accounting
uses typed operand sizes and a 64-byte activation base plus local storage in
`SimpleMaxStackCfg`; counting just call frames would be incorrect.
`block`, `end`, `else` have zero direct opcode cost. Memory/table init, copy,
fill and grow use linear fees; control-flow instrumentation determines when
charges occur, including before traps. Charging once after each executed
instruction is not established equivalent to that instrumentation.

## 3. Complete host surface and gas boundary

The inventory contains **89 production `env` entries**, **11 internal
instrumentation entries**, and **3 excluded build-only entries**. Every entry
includes the import name, implementation name, typed arguments/returns,
configuration gate, build-feature gate and source line. This is the coverage
denominator, not a claim that any host semantics have been implemented.

| Family | Required coverage |
|---|---|
| Registers, context, balances | all read/write/length operations; signer key encoding; refund receiver; chain/epoch/block facts; account contract identifier |
| Hashes/signatures | SHA-256, Keccak-256/512, RIPEMD-160, ecrecover, Ed25519 and P-256 verification |
| Curves | alt_bn128 multiexp/sum/pairing; all nine BLS12-381 entries, including decompression and field-to-curve maps |
| Results/logs/panic | value return, UTF-8/UTF-16 logs, panic, panic_utf8, abort; malformed encodings and size limits |
| Promises | create/then/and, batches, results/return, weighted calls, refund receiver, action creation and all key actions |
| Contract state/actions | deploy/use global contracts by hash/account, deterministic state initialization and data entries, current_contract_code |
| Gas keys | transfer to gas key, add gas key with full/function-call access |
| Yields | ordinary and named yield creation/resume; payload and id validation, cancellation/timeout and queue effects |
| Storage | read/write/remove/has_key, including lazy trie read costs and storage usage |
| Validators | per-account stake and total stake from the current applied epoch |
| Metering | public `env.gas` alias and the eleven `internal.finite_wasm_*` imports |

`storage_iter_prefix`, `storage_iter_range`, `storage_iter_next` are exposed
but return `HostError::Deprecated` (`logic/logic.rs`). Their presence is not
iterator support, and deleting their imports changes link-failure behavior.
`sandbox_debug_log`, `sleep_nanos`, `burn_gas` are excluded in the production
build. Configuration enables the global-contract, gas-key, chain-id, P-256
and named-yield hosts at this pin. `bls12381_not_in_group_fix` remains false;
do not silently adopt different subgroup/error behavior.

Each host needs ordered checks and ordered costs, memory-vs-register input
conventions, integer widths/overflow behavior, pointer bounds, register
effects and error-state effects. Translate `logic/logic.rs`, its helpers and
`runtime/runtime/src/ext.rs`; copying method signatures is insufficient.
The 207-parameter inventory preserves all host/action costs, including
separate gas and compute values. Cross-check their typed runtime export.

`logic/gas_counter.rs` distinguishes burnt gas, reserved promise gas, used
gas, prepaid gas and compute. `deduct_gas`, `burn_gas`, `process_gas_limit`
have checked/wrapping/saturating operations and specific error precedence.
`process_gas_limit` preserves protocol behavior for promise gas on failure;
it prefers `GasLimitExceeded` when both limits are crossed. The Wasmtime
call hooks synchronize a remaining-gas global with this counter. Model
loading costs before/after compilation and all abort paths as well.

Other relevant boundaries: register size 104,857,600 bytes, 100 registers,
aggregate register memory 1,073,741,824; 100 logs / 16,384 log bytes;
arguments/return/storage value limits 4,194,304; storage key 2,048;
1,024 promises, 128 input data dependencies; yield payload 1,024 and timeout
200 blocks. PV86's per-receipt storage proof limit is 4,000,000 bytes.
Large declared limits make sparse memory and adversarial performance tests
necessary; a dense Lean array per allowed byte is not a viable default.

Crypto vector work must record the precise standard, byte encoding,
noncanonical-input policy and vector-set revision for each primitive. Share
SHA-256 and Ed25519 with D1 where their interfaces and behavior match. Vector
success is T evidence only; neither a foreign crypto call nor a table of test
answers can stand in for the trusted Lean specification.

## 4. Runtime and claim integration

The checked-in executable relation is `ChunkValidationV0.checkD0` / `RelD0`;
the runtime is `RuntimeD0`. `WitnessV3.decodeStateWitness` rejects nonempty
transactions/new_transactions and uses the transfer-only receipt decoder.
There is no executable RuntimeD1/RuntimeD2 to import. D3 must either wait for
those deliverables or implement their prerequisites under the same v3
interfaces. Defining `RelD3` as a renamed D0 checker, or accepting a supplied
host result without executing its semantics, would not meet the contract.

Proposed integration is additive: new full action/transaction/receipt codecs,
D3 witness decoding with the existing wire format, and a new runtime/relation
module. Keep existing D0 definitions and fixtures operational. Prove codec
round trips/injectivity for the encodings actually used; retain nearcore's
last-wins receipt-proof HashMap semantics, including decoding overwritten
entries. Do not impose arbitrary canonicalization on nearcore-accepted bytes.

| VM/runtime input | Existing claim/witness source |
|---|---|
| Chain id | T3, checked claim |
| Epoch height, validator stakes | T7/T8 of the epoch of each applied transition |
| Block height/time/randomness | authenticated applied block headers; derive the per-action random seed as `function_call.rs` does from action hash and apply-state seed |
| Signer/predecessor/refund receiver, input/deposit/gas | decoded action receipt and action; apply nearcore's fallback refund receiver |
| Balances, storage usage, local/global code identifiers | authenticated partial trie and prior action state |
| Callback results, output data receivers | input-data trie entries and receipt; output receivers apply to the last action in a batch |
| Contract bodies | existing outer witness `contract_code` list, inserted as hash-addressed TrieValues into the main transition |
| Epoch updates/minimum stake | T10/T11 and authenticated runtime context inherited from D2 |

No new claim field is proposed at this checkpoint. The table is a source
mapping, not proof that every transitive read is covered. Check all
`External` and `EpochInfoProvider` reads during runtime integration; escalate
any newly uncovered fact rather than accepting witness-supplied context.

Source implementation boundaries are `runtime/runtime/src/{function_call,
actions,ext,receipt_manager,global_contracts,contract_code,lib}.rs` and
`core/primitives/src/receipt.rs`. Cover versioned action/data/yield/resume
receipts, deterministic state initialization, gas-key actions, global code
distribution/nonces, postponed receipts, named-yield mappings and timeouts.
These interact with rollback, storage staking, gas/deposit refunds, weighted
gas distribution, receipt IDs, outcomes, outgoing buffers and congestion.
They cannot be implemented solely inside a standalone WASM interpreter.

Missing code is particularly sensitive: during witness validation,
`function_call.rs` turns an absent body for an account committing to code into
`MissingTrieValue`, which rejects the witness. Treating that as an ordinary
contract failure would permit an incomplete witness to establish the wrong
transition. Test omitted, substituted, duplicate and reordered code blobs.

`InD3` must retain the D-infinity exclusions in spec §6: genesis main
transition, dynamic split search, and resharding implicit transitions. An
invalid contract can be an **in-domain failed execution**; do not confuse a
preparation rejection or trap with rejection of the whole witness. Conversely,
do not use an interpreter's temporarily unsupported opcode as the final D3
domain restriction.

## 5. Proposed implementation and evidence sequence

1. **Review this boundary and strategy.** Confirm ownership of the missing
   D1/D2 prerequisites, the interpreter-AIR route, and the independent oracle
   choice below. No change to requirements §§2–5 is requested.
2. **Executable Lean preparation/interpreter.** Add modules under
   `NearSpecV3/Wasm`: bytes/types/codecs; validator; preparation/instrumentation;
   machine/control/stack/memory/table; exact i32/i64/f32/f64 operations; gas;
   typed errors. Use total definitions and explicit resource measures. Fuel
   exhaustion must not silently become a NEAR trap: prove a sufficient bound
   for the represented execution, including zero-cost control steps. Complete
   all accepted proposals before calling the interpreter D3. Prove the codecs
   and determinism/termination properties; compare per opcode and stage.
3. **Hosts and full runtime.** Use an explicit typed host state and effects
   executed by Lean, never host-return-value hints. Connect to authenticated
   trie reads/writes and the full receipt scheduler. Preserve gas on failures
   and transactional rollback boundaries. Add D1/D2 prerequisites before
   claiming full `RelD3`. Export the typed nearcore configuration first.
4. **Three-way evidence.** Extend `oracle/v3` with real D3 chains and its
   existing drop-in validator. Proposed independent lane: a pinned WASM
   reference interpreter with separately implemented host/runtime semantics,
   no nearcore code reuse. Establish support for the entire accepted subset
   and deterministic floats before selecting its revision. Feed all three
   lanes original bytes and the same authenticated context; compare phase,
   exact errors, gas/compute, memory/host effects, receipts, trie roots,
   outcomes/logs and code accesses. Nearcore-prepared bytes are an additional
   instruction test input, not a replacement for testing Lean preparation.
5. **Re-execution admission.** Define the real `RelD3`/`InD3`, retain wire
   formats, then produce a new signed challenge and closed native-Lean
   admission certificate through the existing governance/checker. Do not
   publish a provisional challenge claiming unimplemented semantics.
6. **AIR review and construction.** Use a WASM interpreter AIR; leave L1–L4
   unchanged. Separate instruction fetch/decode, control/operand/call stacks,
   locals/globals, byte memory and tables, exact integer/float operations,
   gas, preparation, hosts, crypto, and receipt/trie transitions. Bind original
   code hashes to authenticated account/global-code state and prove preparation
   or validate its full trace. An unconstrained prepared program breaks
   soundness even if execution is constrained. Use lookup/permutation buses
   for time-indexed reads/writes and existing SHA/trie tables. Review floating
   point and memory consistency with a PoC and concrete column/height budgets
   before committing to layouts. Prove per-table soundness/completeness,
   composition to `RelD3`, justified `Small` bounds, `NpOk`, `Air.wf`, and
   width/fingerprint limits. Do not assert fit before measuring/proving it.
7. **STARK/live hostile admission.** Rust must emit cell-identical honest
   traces. Close the certificate and pass all six real checker gates, then
   all specified live hostile cases. Bind signed reports to artifact hashes.
   Measure proof bytes, proving/verification time and peak RAM for every
   workload and the maximum witness; derive D3 caps through governance.

The random execution campaign must count at least **100,000 executed
function calls**, with zero disagreements in all three lanes. Record seeds,
generator and runner revisions, input/artifact hashes, actual execution counts,
per-category coverage and minimized failures. Do not count preparation rejects
as executed calls, or three reuses of one implementation as three oracles.
Keep held-out cases separate from development data.

Required deterministic categories include every accepted opcode with edge
operands; every excluded proposal; each size/count limit at below/equal/above;
invalid import/export and start behavior; signed zeros, infinities, signaling
and quiet NaNs, rounding/conversion boundaries; memory/table bounds and aliasing;
trap and error precedence; each gas boundary before/during/after host effects;
all 89 public host entries with valid and adversarial arguments; crypto vectors;
deploy/upgrade/global distribution; callbacks and cross-shard promises; ordinary
and named yields/resume/timeouts; storage staking/refunds/rollback; missing
chunks, implicit transitions, queue backlogs and epoch changes. Classify
unreachable engine trap variants separately rather than fabricating executions
of feature-disabled instructions. Add missing-code and missing-read-set mutants.

Run heavy work through `/data/illia/nearproof-deps/bin/heavy`, pinned with
`taskset -c 8-15,24-31`, as the requirements specify. The inventory checks in
this checkpoint are lightweight and do not compile or execute nearcore.

## 6. Review decision and present evidence

The proposed decisions are: implement the full PV86 preparation-v3/Wasmtime
language above; use exact Lean execution and an interpreter AIR; retain all
89 production hosts, including deprecated iterator errors; integrate D1/D2
prerequisites before `RelD3`; and qualify a separate reference-interpreter plus
independent-host lane for the three-way campaign. No narrowing of D3 or claim
format revision is proposed.

Validation performed for this checkpoint: regenerated the source inventory;
checked a byte-identical regeneration; checked signatures/counts/source lines
against the pinned imports; confirmed a modified inventory is rejected. These
checks validate the research artifact only. No Lean proof, WASM opcode
differential run, 100,000-call campaign, AIR proof, performance result, signed
D3 challenge, or live D3 admission is claimed.

The contract's §5.1 says **“Boundary map and strategy (research lane output):
reviewed before implementation.”** This artifact supplies that missing review
input. Lead review is the next required step before semantic implementation;
the remaining work above is explicitly uncompleted.
