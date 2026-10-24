# Complete-code witness policy and preparation/cache closure

Nearcore pin: `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (PV86).
Implementation: `Successor/CodeResolution.lean`. No signed checker is changed by this module.

## The boundary

`CodeWitnessPolicy.coldPartial` retains the earlier successor's code-selection behavior and
cache-dependent exclusion. `complete` is an explicitly different witness relation:

1. Resolve the actual runtime code hash from authenticated account/global state.
2. Probe the **contract trie key** in pre-state without recorder side effects. Keep three outcomes:
   absent, present hash, and unavailable proof path. Unavailable is not absent.
3. When raw code is supplied by the witness store, check its SHA-256 against the resolved hash.
4. When the pre-state key already points at this hash, or the probe is unavailable, require raw
   witness code. A same-code committed, current or rolled-back deployment cannot bypass this check.
5. For a proved new/different code identity, allow authenticated current/committed deployment code.
   A failed deployment's attempted-code list is never a source of executable code in this policy.
6. Missing required code reports `invalid witness (w.code_complete)`. This does not assert that the
   protocol chunk is invalid, or that every warm/cold nearcore process rejects the incomplete bytes.

Complete raw bytes are content-authenticated, not an oracle answer. No compiled artifact, cache
membership, preparation timing or claim-supplied "code valid" flag enters the transition. Production
`mkHStore` authenticates by hash indexing; the resolver also checks each returned candidate explicitly.
The policy does not waive account existence, code-identifier resolution, receipt fees or VM execution.

A canonical artifact builder can append missing pre-state code blobs retrieved by the resolved hash,
then rerun the checker. The existing witness envelope already permits these blobs; no new host-state
fact is needed. Such completion is a witness change and must get its own input hash and oracle run.
Do not count an uncompleted nearcore mutant expectation as the expected verdict for completed bytes.

## Why cold cache alone is not a closed deterministic environment

- `core/store/src/contract.rs:42–69,104–131` reads uncommitted, then committed deployment maps, then
  raw hash-addressed storage. Rollback clears the uncommitted map, not compiled caches.
- `runtime/runtime/src/actions.rs:297–339` writes code, synchronously precompiles, then records the
  deployment. This cache warming survives a later failed action in the same receipt.
- `runtime/runtime/src/pipelining.rs:141–315` prepares function calls asynchronously, up to two
  interesting receipts via `lib.rs:3260–3325`. A prepared missing-code result can precede a later
  identical-code deploy to another account; a different schedule can observe the warmed cache.
- `pipelining.rs:176–190` blocks a receiver when submit encounters DeployContract, UseGlobalContract,
  DeterministicStateInit, CreateAccount or DeleteAccount. DeployGlobalContract does not itself block.
- Postponed calls and yields are not automatically synchronous: `lib.rs:3282–3318` recursively finds
  the pending receipt from Data/PromiseResume and submits it for preparation.
- `pipelining.rs:349` filters prepared artifacts by the resolved code hash. A changed hash is prepared
  again; an equal hash does not invalidate an already-prepared missing-code result.
- `near-vm-runner/src/wasmtime_runner/mod.rs:705–723` uses compiled cache first. Only a miss invokes
  `Contract.get_code`; missing bytes produce ContractCodeNotPresent. During witness validation,
  `function_call.rs:293–305` maps this to MissingTrieValue for deployed-contract accounts.

Therefore replaying the same incomplete code witness with merely an initially empty cache does not
establish universal verdict equality. The complete policy closes missing-byte preparation dependence within a coherent-code cache
environment by requiring authenticated bytes before asynchronous preparation could need them.
It is not a theorem about arbitrary preexisting compiled-cache contents.

## Global distribution caveat

`global_contracts.rs:236–264` writes and commits distribution code and precompiles it, but does not
call `ContractStorage.record_deploy`. A logical materialized-code supply may retain these authenticated
bytes for changed-identity execution; it must not be described as nearcore's literal deploy map.

Although `ReceiptPreparationPipeline.submit` has a distribution branch adding the global identifier
to `block_global_contracts`, the normal `prepare_receipts` helper (`lib.rs:3320`) returns false for
Distribution directly. That branch alone does **not** prove a runtime ordering barrier. The expected
hash check repairs changed code identities. Equal-hash/pre-state calls still require complete raw
witness code to avoid timing-sensitive prepared failures.

## Checked properties and fixtures

`CodeResolutionTests.lean` checks 18 directed cases: cold-partial preservation; raw witness closure;
current/committed/failed same-code deployments; changed-code deployment; rollback; absent versus
unrevealed pre-state probes; bad hash-indexed storage; and present hash references without code blobs.
Theorem `complete_attempted_independent` is definitional: changing attempted deployment history never
changes complete-policy selection. `complete_supplied` proves that authenticated supplied code always
wins regardless of origin/history. Missing raw code at known pre-state or unknown origin is proved to
produce the witness-policy error. These are implementation laws, not axioms assuming a cache answer.

Integration validation must distinguish protocol outcomes from witness-policy failures. Required
independent cases are same-account deploy/call, cross-account identical-code warming, failed deploy
followed by call, postponed/yield preparation and global distribution with equal/changed hashes.
Complete-byte cases must match gas/outcomes/roots; incomplete-byte cases must be explicitly marked as
outside the old cold-validator equivalence comparison. This source/model closure does not by itself
certify every backend/environment error branch or close the full W08 release gate.

## Compiled-code identity boundary

The release implementation of `ContractCode::new(code, Some(hash))` uses a debug-only assertion for
code/hash coherence. A malformed historical global distribution can therefore associate wrong bytes
with a claimed hash in the compiled cache. Raw witness completeness alone cannot make an already
poisoned nearcore cache coherent: a cache hit bypasses the supplied bytes. The successor integration
explicitly excludes malformed current distributions with `out of domain (w.shape): global_code_identity`; historical cache identity
is a separate environment/admission boundary. No theorem in this module establishes equality with
arbitrary warmed or poisoned nearcore histories. `complete_attempted_independent` states only the
exact implemented fact that the attempted-deployment list is not read by complete-policy selection.

## Integrated validation checkpoint — 2026-10-24

The `globalActions` and `completeCodeGlobal` successor tiers now compose the typed actions,
distribution queues, seven promise hosts and recorded execution. Each passes the same 265-case
independent replay: 162 accepts, 99 rejects and four retained key/crypto exclusions. Another 83
promise-host chunks accept in both tiers, including gas exhaustion and child-action failure.
See [integration handoff](../logs/lean-chunk-cache-global-2026-10-24.md).

`tools/d3/check_code_witness_policy.py` separately checks 14 independent complete/incomplete/restored
pairs twice (84 verdicts). Complete and restored bytes accept; incomplete bytes report
`w.code_complete`. The raw incomplete oracle observations remain nine accepts and five rejects,
without relabeling their metadata. Five portable pairs and eight integrity tests are committed;
`make d3-smoke` repeats their 30 policy checks. This establishes tested missing-byte closure under
the stated coherent-code environment, not arbitrary historical compiled-cache equivalence.
