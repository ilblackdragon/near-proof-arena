# D3 (WASM function calls): requirements for an independent workstream

Status: requirements contract, **v0.2 (2026-10-06)**. v0.2 applies the checkpoint-1
corrections (`docs/research/near-wasm-strategy.md` §6, C1–C11) and the user's decisions
recorded in §0.1. Owner of this document: the arena
lead. Implementer: an independent agent/team. Changes to sections 2–5 need the
lead's sign-off because they define what "done" means.

## 0. Why this is separate

D3 adds WASM contract execution to the v3 chunk-validation statement. It is
larger than all other v3 rungs combined. It only needs a narrow, stable interface
with the rest of the project:

* the v3 claim/witness format and relation (`spec/claim-v3.md`,
  `spec/near-chunk-validation-v0.md`, Lean package `NearSpecV3` under `spec/lean/v3`);
* the succinct proof stack (`zk-formal`: L1 field/poly, L2 Fiat–Shamir/BCS,
  L3 IOP soundness, L4 AIR DSL + verifier model; `docs/zk-formal/DESIGN.md`);
* the arena's admission theorem (`formal-core/ArenaCore/Admission.lean`,
  `AdmissionStatement`) and checker rules (`runners/formal-checker/README.md`).

Nothing in this workstream may change those interfaces; it extends them by
adding modules and AIR tables.

Pinned target: nearcore **2.13.4** (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`),
protocol version **86**, mainnet runtime parameters. The research lane
`lane/v3-d3` (`docs/research/near-wasm-boundary.md`, when it lands) is the
starting point for sections 2.1 and 2.2.

## 0.1 Decisions recorded in v0.2 (user, via the lead, 2026-10-06)

1. **Staged domains plus a recursion track.** First deliver D3α (§1.1) end to end, through
   admission (§3). In parallel, run a segmentation and recursion research track inside our proof stack
   (`docs/requirements/RECURSION_REQUIREMENTS.md`). That track must succeed before uncapped,
   mainnet-scale D3.
2. **Floats are out of domain in D3α.** A contract containing any float opcode or float value type is
   out-of-domain. Floats come back in D3β.
3. **`Rel_D3` identifies all error kinds with one failure.** That matches the consensus-visible
   failure bit (`PartialExecutionStatus`, `core/primitives/src/transaction.rs:597-613`). `Rel_D3` is
   exact on success vs failure, gas (burnt/used, compute), refunds, outputs (return value, logs,
   receipts) and state.
4. **`random_seed`, `block_height` and `block_timestamp` are derived from the hash-authenticated
   headers in the claim's chain segment (section B).** nearcore takes them from the applying
   block's header: `ApplyChunkBlockContext::from_header`, `chain/chain/src/types.rs:377-394`, which
   reads `height()`, `raw_timestamp()` and `random_value()`. If any of them turns out not to be
   derivable, a claim-format request is opened; checkpoint 3 confirms this.

## 1. The statement to establish

The v3 relation is `Rel(c, w)`: nearcore's stateless chunk validator, given the
claim `c` (endorsed chunk + authenticated chain segment + itemised trusted facts)
and the witness `w` (the real `ChunkStateWitness` bytes plus contract code), would
endorse the chunk. Domain rungs are `Rel_Dk := Rel ∧ InDk` with
`D0 ⊂ D1 ⊂ D2 ⊂ D3 ⊂ D∞`.

D3 lifts the D2 restrictions on (spec §6, D3):

* `FunctionCall` actions (WASM execution via near-vm-runner, **Wasmtime**
  semantics at PV86: **confirmed**, `core/parameters/res/runtime_configs/84.yaml:2`), including gas
  metering and all host functions;
* `DeployContract`, global contracts, contract code distribution
  (`w.no_code` lifted: contract code blobs are appended to
  `main_state_transition.base_state` as `TrieValues`);
* `Data` receipts, `PromiseYield` / `PromiseResume`, V2 receipts, yield timeouts;
* host functions that read trusted claim facts: `epoch_height` (T7),
  `validator_stake` / `validator_total_stake` (T8), `chain_id` (T3).

D3 does **not** lift (all D3 stages keep these D0–D2 restrictions; lead decision 2026-10-06):

* **resharding** (shard-layout changes, resharding transitions, split gates) stays in D∞. `InD3`
  keeps the single-epoch / no-epoch-start / no-split-gate conditions
  (`spec/lean/v3/NearSpecV3/Wasm/DomainD3.lean`: `noResharding`, `noResharding_spec` and rejection
  examples).

### 1.1 Staged domains (D3α–D3δ, D3∞)

Each stage is a separate `InD3x` with the same claim and witness formats, and each one is a
superset of the previous stage. "Contract" means every contract executed in the chunk (by code hash).

| Stage | Adds | `InD3x` restrictions (decidable from claim + witness) |
|---|---|---|
| **D3α** | integer WASM, all non-curve host functions | no float opcodes or float value types in any executed contract; no `alt_bn128_*`, `bls12381_*`, `ecrecover`, `ed25519_verify`, `p256_verify` imports; per-chunk WASM gas ≤ `G_α` (the cap, set from single-proof capacity; §2.4) |
| **D3β** | + f32/f64 | float restriction lifted |
| **D3γ** | + `ecrecover`, `ed25519_verify` (shared with D1), `p256_verify` | those imports allowed |
| **D3δ** | + `alt_bn128_*`, `bls12381_*` (including the PV86 `bls12381_not_in_group_fix = false` behaviour) | curve imports allowed |
| **D3∞-scale** | uncapped per-chunk WASM gas | needs the recursion track (decision point §2.5) |

`keccak256`, `keccak512`, `ripemd160` and `sha256` are in D3α. They are hash functions, not curve
functions.

The deliverable statement is `Rel_D3` with **the same claim and witness byte
formats** as D0–D2. No new claim fields are allowed unless the lead approves an
additive claim-format revision. If D3 needs a trusted fact that the claim lacks,
raise it as a request.

## 2. What must be proven or established, and at what strength

Every item states its required evidence class: **P** = kernel-checked Lean
proof, no `sorry`/`axiom`/`native_decide`, axioms ⊆ {propext, Classical.choice,
Quot.sound}; **T** = differential testing against nearcore at stated scale;
**T→P** = T now, P is a later stretch goal and must be labelled as open.
Nothing may be reported at a stronger class than achieved.

### 2.1 Executable formal semantics of NEAR's WASM execution (Lean)

Lean 4 definitions (in a new package or `spec/lean/v3/NearSpecV3/Wasm/*`, no
Mathlib in anything the judge trusts) of:

1. **Module validation and preparation** as nearcore performs it at PV86
   (`runtime/near-vm-runner/src/prepare.rs:28-29` → `prepare/prepare_v3.rs`):
   * **Feature set** (validated on the *original* module, `features.rs:71-109`).
     * **In:** MVP; f32/f64 (out of domain in D3α); mutable globals; sign-extension;
       saturating float→int; reference types (**`funcref` only**: `externref` is rejected because
       `gc_types = false`, `features.rs:102`; checkpoint-2 finding); bulk memory.
     * **Out:** multi-value, SIMD, relaxed SIMD, threads, tail calls, multi-memory, memory64,
       exceptions, extended-const, GC, function references, memory control, custom page sizes,
       stack switching, wide arithmetic.
   * **Instrumentation.** nearcore's instrumentation itself emits wide-arithmetic ops
     (`instrument_v3.rs:178-231`). The spec therefore **may** define
     `prepare : Bytes → Except Error PreparedModule`, where `PreparedModule` is the original module
     plus finite-wasm 0.6.1's analysis tables (gas points, operand-stack maxima) plus the prologue
     constants, rather than rewritten bytes. The checkpoint-1 PoC shows this matches nearcore to the
     gas unit.
   * **wasmparser 0.228 implementation limits** (consensus rejections, `Deserialization`): ≤ 50,000
     params + locals per function, ≤ 1,000 params per type, names ≤ 100,000 bytes, br_table ≤ 131,072
     targets, ≤ 100,000 element/data segments. These bind before NEAR's own per-contract limits.
   * **Import/export rules, normalisation and limits.** Imports must come from `env`, function
     imports only. Memory is normalised to `(memory 1024 2048)`. Exports get the `"\0"` prefix. Custom
     sections are discarded. Every limit in `docs/research/near-wasm-boundary.md` §3.2 applies.
   * **Preparation and loading outcomes at PV86** (`fix_contract_loading_cost = false`):

     | Situation | Outcome | Gas burnt |
     |---|---|---|
     | `PrepareError::*`, or `WasmtimeCompileError` (Winch rejects) | failure | **0** |
     | empty method name | failure | 0 |
     | missing method / signature ≠ `[]→[]` | failure, **no-op outcome** | **0** (the loading fee is discarded) |
     | unknown or mistyped import (`LinkError`) | failure | contract-loading fee |
     | instantiation trap (segment out of bounds) | failure | contract-loading fee |
     | loading fee > gas | failure | `min(prepaid, max_gas_burnt)` |

     | `LoadingError`, `WasmUnknownError` (runtime soft-fail) | failure, no-op outcome | 0 (H9) |
     | `ContractCodeNotPresent` | `CodeDoesNotExist` no-op, or `MissingTrieValue` during witness validation if the account commits to code | 0 |

     Sources: `wasmtime_runner/mod.rs:683-923`, `logic/gas_counter.rs:235-270`, `logic/logic.rs:4511-4540`,
     `runtime/runtime/src/function_call.rs:293-337`. Preparation is called from
     `runtime/runtime/src/pipelining.rs:441-450`.
2. **Execution semantics** of prepared modules: a deterministic small-step or
   big-step interpreter over the accepted instruction set, linear memory,
   tables, globals, locals, the call stack with nearcore's limits, traps, and
   **NaN/float determinism**, **determined**:
   * NaN canonicalisation is on (`wasmtime_runner/mod.rs:531-534`, honoured by Winch).
   * The canonical NaN is the positive quiet NaN (`0x7FC00000` / `0x7FF8000000000000`). It is
     applied after f32/f64 add, sub, mul, div, min, max, sqrt, ceil, floor, trunc, nearest, promote and
     demote.
   * `abs`, `neg`, `copysign`, loads, stores, constants and reinterprets preserve bits.

   Floats are excluded from D3α (§0.1) and specified in D3β.
   * **Stack limit.** It is enforced by instrumentation (262,144 accounted bytes: operand-stack
     maximum + 64 + locals per frame). Exhaustion is `HostError::MemoryAccessViolation`
     (`wasmtime_runner/logic.rs:290-292`), not a trap.
   * **Trap mapping.** As `wasmtime_runner/mod.rs:381-413`.
3. **Gas**: instrumentation-injected gas counting, host-function costs from the
   pinned parameter table, `prepaid_gas`/`used_gas`/`burnt_gas` accounting, the
   gas-exceeded and per-receipt-limit semantics, and the mapping to outcomes,
   balances and refunds. Also, explicitly:
   * WASM gas is charged at finite-wasm instrumentation points (whole straight-line ranges, paid up
     front), with Wasmtime call-hook synchronisation (`wasmtime_runner/mod.rs:1042-1072`). **The point
     table is consensus-relevant.** Once a promise exists, an out-of-gas abort charges the whole failing
     range (`gas_counter.rs:118-201`; review F1, reproduced on pinned nearcore), and `burnt_gas` enters
     the outcome root. The spec and **the AIR must charge exactly at the committed finite-wasm points**;
     per-instruction metering is not admissible.
   * **Storage-proof-size coupling.** The per-receipt storage-proof limit (4,000,000 bytes, active
     at PV86, `logic/recorded_storage_counter.rs`) makes execution results depend on witness
     recording. It must be modelled in `RuntimeD3` together with the trie layer.
   * **Compute usage.** It differs from gas for storage and trie costs (compute overrides in the
     parameter table) and drives chunk-level scheduling, so `Rel_D3` must be exact on it.
4. **Host functions.** The coverage denominator is the machine-checked inventory: **89 `env`
   imports at PV86** (`docs/research/near-wasm-boundary-inventory.json`, checked by
   `tools/d3/boundary_inventory.py --check`; table in `docs/research/near-wasm-boundary.md` App. A).
   The split is **78 ungated + 11 runtime-gated** (7 PV85 flags, 4 global-contract functions under the
   PV78 flag `global_contract_host_fns`). The live implementation is
   `runtime/near-vm-runner/src/wasmtime_runner/logic.rs`. The denominator includes:
   * `env.gas`;
   * the three deprecated `storage_iter_*` stubs, which always fail with `Deprecated` and must stay
     linked;
   * `p256_verify`, the gas-key actions, global-contract deploy/use, deterministic state init,
     named yield/resume, `promise_set_refund_to`, `current_contract_code`.

   There is no "math" family. Each host function must have its exact semantics, ordered checks and
   charges (gas is paid *before* bounds checks), argument validation, limits and gas cost. Crypto primitives must be specified
   to their standards (FIPS/RFC/EIP) and shared with D1 where they overlap
   (ed25519, SHA-256).
5. **Integration into `Rel`**: `FunctionCall`/`DeployContract`/promise/yield
   receipts in `RuntimeD3`, producing the same state updates, outgoing receipts,
   outcomes (status, logs, gas, tokens burnt, receipt ids) and trie writes as
   nearcore, and contract-code lookup from the witness.

Evidence class: **definitions** (they are the trusted specification), plus:

| Property | Class |
|---|---|
| Codecs (module bytes, borsh of new receipt kinds) round-trip / injective where used in `Rel` | P |
| Interpreter is total and deterministic (a function; fuel/gas bounds termination) | P |
| Each crypto host function equals its standard spec on standard vectors | T (standard + Wycheproof vectors) |
| Semantics faithful to nearcore's VM (preparation, execution, gas, host functions, outcomes) | T, at scale (2.2) |
| Faithfulness to the WASM spec for the accepted subset (e.g. against WasmCert or the reference interpreter) | T→P |
| Gas-point tables equal nearcore's instrumentation (charge positions and fees), plus a declarative statement of the range-charging invariant next to the port, T-tested against it | T (P stretch) |
| Exact equivalence of the abstract `PreparedModule` (point table, stack charges) with nearcore's instrumented bytes (at least: instrumented size, which decides `InstrumentedCodeTooLarge`) | T |

**Stated assumptions of `Rel_D3`.** These are tested, not provable, and are listed in the spec:

| Id | Assumption | Test obligation |
|---|---|---|
| **H1** | Everything wasmparser 0.228 + finite-wasm accept and NEAR's preparation emits, wasmparser 0.248 + Winch compile, **except the modelled cases** (the spec models the two known rejections: instrumented `params + locals + 2 > 50,000`, and instrumented function body > 7,654,321 bytes; checkpoint-2 finding). The target is pinned to **x86_64/Winch**: the spec states nearcore-on-x86_64 behaviour; aarch64/Cranelift agreement is unmeasured (H11) and an aarch64 difftest leg is recommended. | compile real mainnet contracts and the random corpus; report any unmodelled `WasmtimeCompileError` |
| **H3** | Canonical NaN sign and payload as on x86_64/Winch (D3β onwards) | per-opcode float difftest on x86_64 |
| **H4** | ≤ 262,144 accounted stack bytes never overflow the real native stack before instrumentation traps | deep-recursion stress at the budget boundary, with each frame shape at its maximum |
| H5 | `prepaid_gas ≤ max_gas_burnt` for every function call (otherwise a gas-hook failure becomes `LinkError`) | **P**: derive it from the action-validation spec |
| H2/H10 | Instantiation resource errors (execution-slot semaphore `mod.rs:1012-1018`, pooling-allocator exhaustion, mmap failure) never occur; they would become `LinkError` *with* the loading fee (`mod.rs:414-419, 1019-1026`) | documented only |
| **H9** | No `LoadingError` (corrupted/stale local compiled-contract cache) or `WasmUnknownError`. nearcore turns both into 0-gas failed outcomes (`runtime/runtime/src/function_call.rs:328-337`), so a node where they occur diverges from its peers. `Rel_D3` is stated for a correct node | oracle never shares a persistent cache across versions |
| H12 | Native stack under host calls made at maximum WASM depth does not overflow | stress test (checkpoint 3) |

### 2.2 Faithfulness evidence against nearcore (the oracle)

* Extend `oracle/v3` (`near-arena-oracle-v3`) to produce real chains with D3
  traffic, judged by nearcore's own validator (drop-in criterion (DI) in spec §4).
* Coverage must be stated per category and must include: preparation rejects
  (every limit and feature exclusion), every trap class, gas exhaustion at every
  boundary (including inside host functions), promises/callbacks/yield/resume and
  timeouts, data receipts, storage staking and refunds, every host function
  (honest and adversarial arguments), deploy and global contracts, and
  multi-shard cross-contract calls.
* Random program generation: well-typed random WASM modules (instrumented by
  nearcore's own preparation) plus mutation of real contracts; at least
  **100,000** executed function calls with **0 disagreements** across nearcore,
  the compiled Lean semantics, and one independent implementation.
  **Independence scope.** The WASM core (decode, validate, execute) and the host-function logic are
  each checked against an independent implementation that is not derived from nearcore's code (for
  example the WASM reference interpreter or WasmCert's extracted interpreter, plus independently
  written host code). Gas metering is *defined* by finite-wasm's algorithm; independence is obtained by a
  **clean-room reimplementation from a short prose specification** of the range-charging rule, written by
  a different author (≈1–2k LOC), compared against both the Lean port and nearcore.
* Required case families include promise creation followed by out-of-gas inside a long range (review F1),
  `value_return` with non-empty output data receivers, and `compute_usage` and `logs` in the comparison
  (from checkpoint 3).
* Comparison is on exact `VMOutcome`s, including the error variant, even though `Rel_D3`
  identifies error kinds (§0.1.3). The quotient is a property of `Rel`, not a relaxation of the
  tests.
* Instruction-level differential tests (per opcode, edge values) against the
  pinned VM.
* Every out-of-D3 case (D∞ features) must be rejected by `InD3`.

### 2.3 Succinct proof of `Rel_D3` (STARK, admitted like np-udr-stark)

The recommended design is in `docs/research/near-wasm-strategy.md` §2: a universal machine AIR over a
flat prepared IR, with grand-product RAM consistency, preparation as its own AIR on the L5/L6 buses,
and host chips on buses. Checkpoint 5 reviews it.

The prover must be accepted under the arena's existing `AdmissionStatement`.
It reuses L1–L4 unchanged. New work is AIR tables plus their proofs:

1. **AIR design** for WASM execution, with an explicit choice and
   justification: (a) a WASM-interpreter AIR (instruction fetch/decode, operand
   stack, locals, control flow) with memory consistency by permutation/lookup
   arguments; (b) anything else. A compile-to-RISC-V + zkVM route is not
   acceptable unless the compiler step is itself proven (P).
2. For every new table, in L4's DSL, mirroring L5/L6:
   * **Soundness (P):** `Holds air (publicOf c) tr → ∃ w, Rel_D3 c w`, composed
     from per-table lemmas: execution trace ⇒ semantics of 2.1, memory/stack
     consistency arguments, gas accounting, host-function tables, and the bus
     contracts with SHA-256 (L5), trie (L6) and v3 D0–D2 tables.
   * **Completeness (P):** every `Rel_D3` instance (within stated `Small`
     bounds, which must be justified like L6's) has an honest trace satisfying
     the AIR, and the trace fits the height bounds.
   * Side conditions for L3 (`NpOk`) and L4 (`Air.wf`, width/fingerprint
     budgets) (P, kernel `decide`).
3. **Certificate (P):** a closed `AdmissionStatement` for the D3 challenge
   (native-lean route at minimum; bytecode/NPAI route optional), passing the
   real formal checker on all six gates, with all audits (axiom audit, csimp
   audit, no `initialize`/`register_*`/`import Lean` in candidate modules,
   trusted tree pinned).
4. **Prover (Rust):** trace generation cell-for-cell equal to the Lean honest
   trace on all oracle cases, proofs accepted by the judge-built verifier,
   rejection of all adversarial mutants (arena `proof-mutators` plus
   WASM-specific: forged memory reads, skipped gas, wrong host results, trace
   reordering).

### 2.4 Performance requirements (succinctness is first-class)

Ranking uses the cost-normalized board (lane `scoring-v2`): prover time plus
validator fan-out × (verify time + bandwidth × proof bytes) under the governed
price model. Hard caps from the challenge (current v1 values for reference:
proof ≤ 8 MiB, verify ≤ 10 s, prove ≤ 600 s per request at the challenge's
hardware profile, peak memory ≤ 16 GiB). The D3 challenge will set its own caps
from measured reference costs. Report, per workload class and at the
adversarial maximum witness: prove time, peak memory, proof bytes, verify time.
Recursion/compression to reduce proof size is in scope if it is proven under
the same formal stack.

**D3α gas cap `G_α`.** One np-udr-stark proof (tables ≤ 2^22 rows) holds roughly 1–3 Tgas of pure
WASM, while a chunk may burn up to 10^15 gas (≈1.2·10^9 operators at `regular_op_cost` = 822,756).
`G_α` is fixed at checkpoint 5 from the measured EXEC/RAM rows per operator, and the D3α challenge's
caps come from it. Workload classes must include a max-`G_α` class.

**Contract size vs table height (review §3.7).** A maximum-size contract (4,194,304 bytes) needs at least
one PREP row per byte, already more than 2^22 rows. D3α must either segment PREP or carry an `InD3α`
code-size cap fixed at checkpoint 5. Also in scope for the risk register: variable-cost storage gas
(trie-node charges depend on chunk-level access history), the bn254/BLS12-381 *specification* work
(map-to-curve, `not_in_group` behaviour, per-item cost formulas), promise-DAG/yield semantics, and
compute usage (it is derived from `burnt_gas`, so it inherits the point-table dependence).

### 2.5 Decision point: segmentation and recursion (required for D3∞-scale)

Uncapped D3 needs execution segmentation (continuations) **and** a way to compose segment proofs
that is admissible under `AdmissionStatement`. A plain recursive verifier-in-AIR is known not to be
provable in the ROM branch (`docs/zk-formal/V3-D0-DESIGN.md` §5.5). The research track and its
acceptance criteria are in `docs/requirements/RECURSION_REQUIREMENTS.md`. Before the D3∞-scale
challenge is drafted, the lead decides among:
(a) an admissible composition was found, so build D3∞ on it;
(b) no admissible composition, so D3 stays capped, with `G_α` raised only through prover and
parameter work (larger tables, multi-table segments within one proof).

## 3. Acceptance criteria ("done")

D3 is complete when **all** of these hold:

0. Staging: criteria 1–5 apply **per stage**, starting with D3α. "D3 complete" means D3δ plus the
   §2.5 decision resolved.
1. `Rel_D3` and `InD3` are defined in Lean. Every property in 2.1 marked P is
   proven; every T property meets 2.2's scale with 0 disagreements; and
   `docs/research` plus the spec document what is P versus T.
2. A signed D3 challenge (local operator key under the current governance
   flow) pins the trusted tree, checker identity, workloads (including a
   max-witness class), held-out set and baseline.
3. A re-execution reference candidate (native-lean, `decide Rel_D3`) is
   ADMITTED live at formal tier.
4. A succinct STARK candidate is ADMITTED live at formal tier on the same
   challenge, with all gates PASS, a signed artifact-bound report, and the
   performance numbers in 2.4.
5. A hostile suite for D3 runs live with every case rejected at its intended
   gate: an unsound AIR (missing memory-consistency constraint), wrong gas
   accounting, a host function returning a wrong value, an unaudited `@[csimp]`,
   a stale trusted tree, and an out-of-domain contract feature.

## 4. Non-goals and constraints

* Not zero-knowledge. Validity only, unless a separate privacy requirement is
  issued.
* No changes to frozen v1/v2 files or to signed challenges. v3 files are
  additions.
* No Mathlib in trusted modules. Candidate proofs may use it only if the
  challenge allows a pinned revision.
* No `native_decide`, `implemented_by`, `extern`, `@[export]`, `initialize`,
  `unsafe` or `partial` in the certified path. Compiler rewrites only as
  kernel-proven `@[csimp]`.
* Host resource rules on the shared machine: heavy commands go through
  `/data/illia/nearproof-deps/bin/heavy`, pinned with `taskset -c 8-15,24-31`.

## 5. Checkpoints (report to the lead at each)

1. Boundary map and strategy (research lane output): reviewed before
   implementation. **Done 2026-10-06** (`lane/v3-d3`: `near-wasm-boundary.md`,
   `near-wasm-strategy.md`, the PoC with 7,000 cases and 0 disagreements).
2. Lean semantics for the accepted instruction subset (**D3α: integer WASM incl. tables,
   `call_indirect`, globals, bulk memory, reference types**), plus the per-opcode
   difftest. **Reported 2026-10-06** (`docs/research/d3a-checkpoint2.md`: 73,049 compared
   cases, 0 disagreements; host functions beyond 5 are checkpoint 3).
3. Host functions, gas and outcomes, plus the full-runtime difftest at scale
   (2.2).
4. `Rel_D3` plus the re-execution reference ADMITTED live.
5. AIR design review (tables, budgets, PoC of the riskiest table).
6. AIR soundness and completeness closed; Rust prover conformance.
7. STARK candidate ADMITTED live; hostile suite green.

## 6. Change log

* **v0.2 (2026-10-06)** applies checkpoint-1 corrections C1–C11 (`docs/research/near-wasm-strategy.md` §6) and the user decisions in §0.1:
  * staged domains D3α–D3δ (§1.1);
  * the x86_64/Winch pin and assumptions H1–H5 (§2.1);
  * the exact feature list, and an abstract `PreparedModule` (§2.1.1);
  * the zero-gas / loading-fee table (§2.1.1);
  * the NaN rule (§2.1.2);
  * storage-proof-limit and compute-usage coupling, and `metering_equiv` (§2.1.3);
  * the 89-import inventory as the coverage denominator (§2.1.4), split 78 + 11;
  * after the independent review (`docs/reviews/D3_REVIEW_2026-10-06.md`): F1, the point table is
    mandatory and `metering_equiv` is retracted; F2, H9 and the soft-fail rows; F6, the wasmparser triple and
    0.228 limits; F7, the counts; F12, the `pipelining.rs` citation; H10–H12; C9, clean-room metering;
  * the scope of the independent-implementation requirement (§2.2);
  * the `G_α` cap (§2.4);
  * the segmentation/recursion decision point (§2.5);
  * per-stage acceptance (§3).

  C11 (no `partial` in the certified path) needed no change.
* v0.1 (2026-10-05): initial contract.
