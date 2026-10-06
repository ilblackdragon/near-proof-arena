# D3α checkpoint 3: progress report (in progress, not complete)

Status: interim report, 2026-10-06, lane `lane/v3-d3`. Requirements: `docs/requirements/D3_WASM_REQUIREMENTS.md`
v0.2 §5 checkpoint 3 ("host functions, gas and outcomes, plus the full-runtime difftest at scale").
Evidence labels: **[T]** tested against pinned nearcore; **[src]** read in source; **[P]** kernel-checked.

## 1. Done: VM-level host semantics

**Specification.** New modules under `spec/lean/v3/NearSpecV3/Wasm/`:
* `Machine`: machine state, the gas counter, and the **gas profile** (`ProfileDataV3`), which makes
  `compute_usage` exact (`profile.rs:98-175`: per-`ExtCosts` slots for the 11 costs whose compute ≠ gas,
  action gas, `send_action_compute_usage`, wasm gas).
* `Crypto`: Keccak-256/512 (Keccak-f[1600], original padding) and RIPEMD-160. SHA-256 is the trusted
  `NearSpec.sha256`.
* `Host`: **all 75 non-curve host functions** of PV86 (89 importable − 14 curve functions):
  * registers, context getters, economics, validator stake;
  * sha256, keccak256/512, ripemd160, and `ed25519_verify` (on **D1's** `NearSpecV3.Ed25519.verify`, merged
    from `lane/v3-d1-crypto`);
  * logs: log_utf8, log_utf16, panic, panic_utf8, abort;
  * storage: write/read/remove/has_key, and the three deprecated iterators;
  * promises: create/then/and/batch_create/batch_then/set_refund_to, plus every batch action, including
    global contracts, deterministic state init and gas keys;
  * results/return, yield/resume (with and without an id), and `gas`.

  Each one follows nearcore's order of charges and checks. Curve host functions
  (`alt_bn128_*`, `bls12381_*`, `ecrecover`, `p256_verify`) put a contract **out of domain**. The
  `External` used here is nearcore's own `MockedExternal` semantics: storage map, action log, data
  ids.

**Oracle.** The harness has a new mode `full` that also prints `compute_usage`, the logs, the canonical
action log and the final storage. The context can be varied per case: input, promise results,
attached deposit, balance, and output data receivers.

**Results [T]** (pinned nearcore 2.13.4, x86_64; full outcome lines, including compute/logs/actions/storage
for `host` and `hostedges`):

| Family | Cases | Disagreements |
|---|---|---|
| `host`: random host-call sequences, args chosen by parameter role, seeds 1–12 (final build) | 48,000 | **0** |
| `hostedges`: every limit error, deep success paths, gas keys, 400 nearcore-judged Ed25519 vectors | 442 | **0** |
| `promise` and `random` in full mode (compute usage, logs) | 5,000 | **0** |
| regression after the refactor: `opcodes`, `random`, `promise` | 15,167 | **0** |
| `mutate`, seeds 21–59 (byte-level mutants; decode/validate/limit-order agreement) | 285,000 | **0** (after the fixes below) |

Preparation-fidelity findings from the larger mutation run [T]. All are fixed and re-tested.

1. **Consensus-relevant spec bug.** The memory index of `memory.init`/`memory.copy`/`memory.fill` is a LEB
   u32 (`0x80 0x00` is valid). The spec required a single zero byte, so it **rejected contracts that
   nearcore accepts**. The random generators always emitted canonical bytes; byte-level mutation found it.
2. A function body's locals reader is bounded by the body size. A zero-size body is `Deserialization`,
   not a read into the next body.
3. Local value types are parsed by wasmparser's *permissive* reader (GC syntax, s33 type indices, v128).
   NEAR's local budget is checked between parsing and validation, so `TooManyLocals` can precede a
   type error.
4. The code section is streamed. A truncated code section reports `TooManyFunctions` (count vs.
   budget) before the truncation.
5. Trailing bytes in the import or table section are detected by the validator **before** NEAR's
   import/table checks.

Findings while doing this [T]:
* the initial balance is `account_balance + attached_deposit` (`logic/logic.rs:66-70`);
* Rust `{:?}` writes `\0` for NUL (`GuestPanic` messages);
* the amount pointer of a function-call action is read with `get_u128`, which has no register path.

## 2. Done: F11 and parts of F5

* **F11:** `compute_usage` and logs are now compared, in every `host`/`hostedges` case and in full-mode runs of
  the other families. 0 disagreements.
* **F5/C9: done for metering and the checkpoint-2 subset.**
  * **Prose spec.** `docs/research/near-wasm-prose-spec.md` specifies NEAR's metering, preparation and
    execution, with errata in §7.
  * **Clean-room implementation.** A separate agent wrote `oracle/wasm-d3/cleanroom/nearwasm.py` (Python,
    standard library only) from that spec. It had no access to finite-wasm, nearcore's instrumentation or
    the Lean spec, and settled ambiguities by black-box runs.
  * **Three-way outcome agreement [T]:** nearcore = Lean = clean-room on opcodes (9,175), promise (3,000),
    mutate (10,000) and random (1,500), with **0 disagreements**. The clean-room's own runs add a further
    ~95,000 cases.
  * **Charge-point tables:** the clean-room tables equal the Lean (finite-wasm-port) tables on 12,845 of
    13,363 modules. The other 518 differ **only** in placing a point one operator earlier, at the zero-cost
    `end` that closes a dead region. The fees are identical and the outcomes agree (prose §7 D13).
  * **Spec bugs it found in the Lean spec [T]** (now fixed and in `opcases`):
    * a table with initial size > 10,000,000 must give `TooManyTableElements`, not `Deserialization`;
    * a non-memory export name of ≥ 100,000 bytes must give `PrepareError::Serialization` (NEAR's `"\0"`
      prefix exceeds the re-parse's 100,000-byte limit).
  * The clean-room's scope is still core, metering and the checkpoint-2 host functions. Independent
    implementations of the other 70 host functions are still open.

## 3. Not done, and the blocker for RuntimeD3

* **RuntimeD3 integration** (FunctionCall, DeployContract, Data and yield receipts, refunds, outcomes) is
  **not started**. It needs two things the VM layer does not provide:
  1. **The real `External`:** trie access through `RuntimeExt` (`runtime/runtime/src/ext.rs:147-313`).
     Its gas includes `touching_trie_node`/`read_cached_trie_node` charges, computed from trie-node read
     counts of the chunk's accounting cache (`commit_counts_since`, `ext.rs:700-725`) in flat-storage
     mode (`StorageGetMode::FlatStorage`). It also includes the per-receipt recorded-storage limit
     (H8). This has to be specified on top of the v3 trie layer (`TrieBuild`/`PTrie`). It is the
     largest single remaining specification item for D3α.
  2. **All non-WASM action and queue semantics:** create account, transfer to implicit accounts, keys,
     delete account, stake, data receipts and postponed receipts, delayed queues, yield timeouts,
     refunds. A function call emits arbitrary action receipts, and these are D2's scope (requirements
     §1: "D3 lifts the D2 restrictions").

  **Open question for (1)** [src]:
  * Contract storage reads use `KeyLookupMode::MemOrFlatOrTrie` (`ext.rs:197-200`). The accounting
    cache doc says flat-storage reads are *not* tracked, except for value dereferences
    (`ext.rs:676-679`).
  * Stateless validators have no flat storage; they read a recorded partial trie.
  * How nearcore keeps `touching_trie_node` counts identical between producer and validator (memtries
    on both sides, or recording rules) must be settled from source plus TestEnv evidence before
    the trie-accounting `External` is specified.

  **Escalation:** building `RuntimeD3` on `RuntimeD1` alone would re-implement D2. The proposal is that
  `RuntimeD3` waits for `RuntimeD2` (or D2's action/queue modules land first). Until then, D3 work can
  proceed on (1), the trie-accounting `External`, which D2 does not need.
* **The 100k full-runtime difftest:** depends on the above, plus `oracle/v3` producing chains with WASM
  traffic.
* **N3** (`xs[i]!` cleanup), partly done:
  * `Host` is clean: host arguments are `Vector`s, so access is statically in bounds.
  * The execution path in `Exec` reports explicit `unmodeled "invariant: …"` instead of defaulting.
  * Still to do: preparation-time indexing in `Prepare`/`FiniteWasm`/`InstrSize` (indices are validated
    by then) and bounded loops in `Exec`/`Machine`/`Crypto`.
* **Independent implementation for host functions (§2.2):** not started. The clean-room agent's scope is
  core + metering + the checkpoint-2 host functions.
