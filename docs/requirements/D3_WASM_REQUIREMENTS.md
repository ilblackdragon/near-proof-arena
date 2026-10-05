# D3 (WASM function calls): requirements for an independent workstream

Status: requirements contract, v0.1 (2026-10-05). Owner of this document: the arena
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

## 1. The statement to establish

The v3 relation is `Rel(c, w)`: nearcore's stateless chunk validator, given the
claim `c` (endorsed chunk + authenticated chain segment + itemised trusted facts)
and the witness `w` (the real `ChunkStateWitness` bytes plus contract code), would
endorse the chunk. Domain rungs are `Rel_Dk := Rel ∧ InDk` with
`D0 ⊂ D1 ⊂ D2 ⊂ D3 ⊂ D∞`.

D3 lifts the D2 restrictions on (spec §6, D3):

* `FunctionCall` actions (WASM execution via near-vm-runner, **Wasmtime**
  semantics at PV86 — confirm from source), including gas metering and all
  host functions;
* `DeployContract`, global contracts, contract code distribution
  (`w.no_code` lifted: contract code blobs are appended to
  `main_state_transition.base_state` as `TrieValues`);
* `Data` receipts, `PromiseYield` / `PromiseResume`, V2 receipts, yield timeouts;
* host functions that read trusted claim facts: `epoch_height` (T7),
  `validator_stake` / `validator_total_stake` (T8), `chain_id` (T3).

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

1. **Module validation and preparation** as nearcore performs it at PV86:
   accepted feature set (which WASM proposals; float ops, SIMD, bulk memory,
   reference types, multi-value: each explicitly in or out), import/export
   rules, size and count limits, and the **instrumentation** (gas-metering
   injection, stack-height limiting) as a transformation `prepare : Bytes →
   Except Error PreparedModule`. The relation must treat preparation failures
   exactly as nearcore does (outcome, gas, refunds).
2. **Execution semantics** of prepared modules: a deterministic small-step or
   big-step interpreter over the accepted instruction set, linear memory,
   tables, globals, locals, the call stack with nearcore's limits, traps, and
   **NaN/float determinism** exactly as executed by nearcore's VM (canonical NaN
   rules, or float ops excluded — determine and match).
3. **Gas**: instrumentation-injected gas counting, host-function costs from the
   pinned parameter table, `prepaid_gas`/`used_gas`/`burnt_gas` accounting, the
   gas-exceeded and per-receipt-limit semantics, and the mapping to outcomes,
   balances and refunds.
4. **Host functions**: every import nearcore exposes at PV86 (storage
   read/write/remove/has_key/iterators if any, promises/batches/yield/resume,
   registers, logs, return data, context: account ids/balances/attached
   deposit/block height/timestamp/epoch height/validators/chain id, crypto:
   sha256/keccak256/keccak512/ripemd160/ecrecover/ed25519_verify/alt_bn128/
   bls12-381 if enabled, math, panic/abort, …), each with its exact semantics,
   argument validation, limits and gas cost. Crypto primitives must be specified
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
  the compiled Lean semantics, and one independent implementation (not derived
  from nearcore's code, e.g. the WASM reference interpreter plus independent
  host-function code).
* Instruction-level differential tests (per opcode, edge values) against the
  pinned VM.
* Every out-of-D3 case (D∞ features) must be rejected by `InD3`.

### 2.3 Succinct proof of `Rel_D3` (STARK, admitted like np-udr-stark)

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

## 3. Acceptance criteria ("done")

D3 is complete when **all** of these hold:

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
   implementation.
2. Lean semantics for the accepted instruction subset, plus the per-opcode
   difftest.
3. Host functions, gas and outcomes, plus the full-runtime difftest at scale
   (2.2).
4. `Rel_D3` plus the re-execution reference ADMITTED live.
5. AIR design review (tables, budgets, PoC of the riskiest table).
6. AIR soundness and completeness closed; Rust prover conformance.
7. STARK candidate ADMITTED live; hostile suite green.
