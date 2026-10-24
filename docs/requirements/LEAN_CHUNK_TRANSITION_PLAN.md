# Full NEAR chunk transition in Lean and arena completion

Date: 2026-10-23. Status: in progress; merged checkpoints recorded below, no completion gate certified.
Baseline: `05aee4479`. Sponsor direction: finish a proof-system-independent Lean chunk transition
and arena so different succinct proof approaches can be researched against the same specification.

> **Initially merged onto `main` 2026-10-23 as a plan only.** This document and its `docs/HANDOVER.md` pointer
> were merged; **no gate, milestone or workstream here is thereby certified**, and gates A/B/C remain
> open exactly as the completion record at the end of this file states. Two things a reader on `main`
> should know: (1) the `05aee4479` baseline is the *plan's* baseline, not `main`'s tip — `main` has
> moved substantially since (MEMIO, prepare-link, aggregation, D0a profiling), so §2's "what already
> exists" should be re-resolved against current source before reuse; (2) the "Start:" paths in §4 were
> checked to exist at merge time, and the figures in §2 (115,284 D3 cases; 407 public / 208 held-out)
> are corroborated by `docs/logs/v3-progress-log-2026-10.md`, `spec/near-chunk-validation-d3.md` and
> `docs/e2e-results/` — they are carried forward as cited evidence, not re-measured here.

### Completion execution — 2026-10-24 (W05 excluded)

The [completion workplan](LEAN_CHUNK_COMPLETION_WORKPLAN.md) and
[execution log](../logs/lean-chunk-completion-2026-10-24.md) track the newer implementation:
strict successor replay, pinned Wasmtime instance loading semantics, and generated float runtime /
whole-chunk coverage. Six driver executables and seven configurations now have build/smoke coverage;
recorded runtime regressions replay in CI without the external corpus. W05 remains with its owner.
No Gate A/B/C closure is claimed; full semantic integration, proofs, representative witnesses,
frozen validation and admission remain required. The snapshot below is historical.

### Progress snapshot — main at `e34852568` (2026-10-23)

L0–L7 now have merged checkpoints. L1's above-cap example, L4's directed tests and exclusion replay,
L6's corrected genesis checker, and L7's deeper audit/CI wiring have landed since `b2f83fe76`.
L8 has no additional committed implementation checkpoint. Lane worktrees remain available for
continued development and reconciliation. **No lane is certified complete.** Checked items in §4
record sub-deliverables, not satisfaction of the full acceptance criteria.

The [completion workplan](LEAN_CHUNK_COMPLETION_WORKPLAN.md) gives the remaining deliverables,
success criteria, shared interfaces and dependency graph for parallel implementation. It separates
work that can start now from acceptance dependencies and the final combined validation/release gates.

The [first integration record](../logs/lean-chunk-integration-2026-10-23.md) identifies the exact
`b2f83fe76` lane tips and checks; its L6 holdback is superseded by the corrected merge. Subsequent
progress is recorded below. Historical full replay results remain carried-forward lane evidence,
not a fresh full replay of one combined successor. The v3 CI build and harness tests are wired;
the new corpus-manifest job still needs corpus provisioning, and not every successor target is in
the default build. These remaining CI obligations are W01 in the completion workplan.

## 1. Objective and target

Deliver an executable Lean specification of the full chunk state transition at the repository's
pinned target: nearcore 2.13.4, commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol
version 86, pinned mainnet runtime parameters. Deliver a reproducibly built re-execution reference
admitted by the arena, with versioned workloads and an explicit semantic coverage contract.

“Full” means every protocol-valid case at this target and validator boundary is handled, including
failures, storage limits, cryptographic operations and resharding. It does not mean all future
protocol versions. Cases impossible at this boundary must be justified from the pinned validator,
not silently excluded. The boundary audit below must settle genesis and chain-segment cases.

The arena must admit alternative proof systems through the existing artifact-bound admission
contract. Completing an AIR, recursive verifier, PQ construction or GPU prover is not a prerequisite
for completing this plan. A succinct candidate is not required to close the reference/arena milestone.
This deliberately separates milestones that the older D3 requirements combined.

The current signed challenge remains immutable. Broader semantics, claim formats, coverage rules,
gas limits or scoring changes belong to a versioned successor. Signing, deployment and publication
follow existing operator authorization; this plan alone does not authorize those external actions.

## 2. What already exists

The D3α checker executes a whole chunk in a restricted domain. D2 supplies transactions, actions,
receipts, queues, refunds, congestion/bandwidth handling, trie operations and validator updates;
D3 adds prepared integer Wasm and contract execution through the D2 hooks. The Lean interpreter is
more complete than the current Wasm AIR: AIR gaps are not evidence of missing Lean semantics.

Evidence already recorded, to be reproduced or explicitly carried forward with hashes:

* D3 differential corpus: 115,284 cases, zero disagreements in the recorded three-way comparison.
* Re-execution reference: reproducible verifier build, configured formal checking and public/held-out
  conformance evidence. The 2026-10-14 presign run records 407 public and 208 held-out positives,
  244 public and 64 held-out rejections, and 3,062 public plus 1,433 held-out mutations rejected.
* Explicit artifact soundness landed in `ReexecV3D3/ArtifactSound.lean`. The unconditional decoded
  statement concerns canonical re-encoding; a statement on original bytes needs canonicality.
* The unified challenge was signed and deployment is documented. A final live D3 reference admission
  must be verified from the actual signed report; deployment is not admission.

These facts do not establish full PV86 coverage or a formal equivalence theorem with nearcore.
The existing Python VM was tuned against nearcore; do not describe its agreement as independent
specification validation without explaining that provenance.

Starting sources:

* [Handover](../HANDOVER.md) — mixes historical snapshots; resolve claims against source/evidence.
* [D2 domain and implementation](../../spec/near-chunk-validation-d2.md), especially §§12–13.
* [D3 domain and implementation](../../spec/near-chunk-validation-d3.md), especially §10.
* [D3 requirements](D3_WASM_REQUIREMENTS.md) — existing staging and trusted-code rules.
* [D3 presign evidence](../logs/v3-d3-presign-2026-10.md).
* [D3 artifact soundness](../logs/d3-artifact-soundness-2026-10-22.md).
* [Unified challenge deployment](../logs/v3-deploy-v3-2026-10.md).

## 3. Exact success gates

### Gate A — restricted research arena ready

All of the following must hold. This gate can close before full semantic coverage.

- [ ] The immutable D3α relation, trusted tree, parameters and declared exclusions are identified by hashes.
- [ ] A clean build of the exact reference passes every configured formal gate, including artifact
  binding and independent kernel rechecks, within the judge's enforced budgets.
- [ ] Public and held-out conformance, adversarial, reliability and resource gates all pass on that
  same package. Record aggregate held-out counts only.
- [ ] The live judge returns **ADMITTED at formal tier** for that exact reference; archive the signed
  report, challenge/submission/run IDs and verifier digest. Historical local PASS is insufficient.
- [ ] An external candidate can follow documented prepare/prove/verify and certificate instructions
  from a clean checkout using the published allowed inputs, without importing the current AIR/PQ stack.
- [ ] The board reports declared semantic coverage and measured proof bytes, verification cost and
  proving resources. Any succinct badge is backed by explicit signed thresholds and its enforced test;
  otherwise leave it unset. Re-execution must not be presented as succinct.

### Gate B — full executable PV86 transition

- [ ] The coverage inventory accounts for every validator branch, action/receipt/key variant,
  accepted Wasm instruction family, host function, resource boundary and inherited domain guard.
- [ ] Every reachable supported-protocol row is implemented and validated. There are zero unresolved
  `unmodeled`, unsupported, or research-only domain exclusions for valid inputs at the target boundary.
- [ ] Impossible cases have an explicit pinned-source justification and a checked predicate or
  theorem where expressible. Merely renaming an exclusion does not close it.
- [ ] The canonical relation covers protocol-scale chunks. It has no `G_α` or other bound derived
  from one prover's table height, width, recursion shape or performance budget.
- [ ] Actual protocol resource limits and their failure/rollback behaviour are implemented rather
  than replaced by bounds that make those paths unreachable.
- [ ] All per-lane tests and the combined regression/replay gates in §5 pass with zero unexplained
  disagreements. Timeout, crash, truncation and missing results are failures, not out-of-domain verdicts.
- [ ] All trusted assumptions are enumerated, including authenticated external facts and runtime
  environment assumptions. No missing transition semantics are hidden as an assumed result.

### Gate C — full transition arena released

- [ ] Gate B and the successor's equivalent of every Gate A check pass on one frozen release.
- [ ] A single canonical full relation is the semantic root. Each successor coverage tier is a
  restriction of that relation, with proved inclusion, rather than a separate trusted transcription.
- [ ] Claim/witness encodings, canonicality, public binding and authenticated fact provenance are
  specified and checked. No state-transition result is accepted merely because it is supplied as a fact.
- [ ] The successor challenge pins the trusted root, oracle, workload definitions, held-out commitment,
  resource profile, coverage semantics and measured scoring baseline; it is signed and deployed.
- [ ] Its re-execution reference is ADMITTED live at formal tier, with a signed artifact-bound report.
- [ ] The contributor guide demonstrates how a different proof system proves the same admission
  statement and declares partial coverage without modifying the trusted transition relation.
- [ ] The release explicitly distinguishes machine-checked candidate-to-Lean soundness from tested
  Lean-to-nearcore correspondence. No formal nearcore equivalence claim is made without that theorem.

## 4. Workstreams and ownership boundaries

Workstreams were initially unassigned; the lane logs and integration record now identify the
active checkpoints. Claim or reconcile ownership in a lane log before editing shared modules. No lane may report completion using only a README, an axiom-clean conditional theorem,
or a successful test that never exercises the new semantic path.

### L0 — boundary and coverage inventory

**Progress through `e34852568`:**

- [x] Merged the inventory, readable boundary analysis and drift-gated generator; the initial combined inventory had **219 unique rows** (`1d242e6c2`); it now has **222** after the L6 additions.
- [ ] Resolve outstanding boundary questions and exclusions; inventory existence does not establish exhaustive validated coverage.

Evidence: [L0 log](../logs/lean-chunk-L0-2026-10-23.md), [current inventory](../research/lean-chunk-coverage.json).

Start: `spec/lean/v3/NearSpecV3/{ChunkValidationD2,D3/FunctionCall,Wasm/Exec}.lean`, the domain
specifications, pinned nearcore `validate_chunk_state_witness`, claim codec and trusted-fact schema.

Deliver `docs/research/lean-chunk-coverage.json` and a readable summary. Each row must contain:
`id`, `family`, `nearcore_commit`, `nearcore_path_symbol`, `lean_path_symbol`, `status`,
`domain_guard`, `evidence`, `owner`, `dependencies`, `acceptance_tests`, `remaining_work`.
Allowed statuses: implemented, partial, missing, impossible-at-boundary, validated.

Acceptance: enumerate all current rejection/domain guards and every branch/variant in the pinned
validator boundary; reconcile requirements versus actual dispatch (especially called versus imported
hosts). Resolve genesis, segment/layout restrictions, scheduler assumptions, cache dependence and
claim facts. Every remaining item maps to a lane below or a newly named lane. Publish unresolved
boundary questions explicitly; Gate B cannot pass with one unresolved.

### L1 — canonical relation and prover-independent capacity

**Progress through `e34852568`:**

- [x] Merged the additive protocol-gas successor and axiom-free cap comparison facts (`a5ef42e0c`); signed `RelD3`/`gAlpha` remain unchanged.
- [x] **Demonstrated an accepted chunk above the old cap.** `d3c7/ood/00-h10007-s1` (`meta.json` `expected_rel: true`, sole violation `e.g_alpha`) is `out_of_domain` under `checkD3` and **`accept`** under the new `checkD3Proto` (`nearspec-v3-check-d3proto`, merged `c73f92347`). 846 protocol-valid chunks sit in the band across the four corpora. Overlap agreement sampled 12/12 across accept/reject/out-of-domain; band acceptance sampled 25/25. All measured, not proved.
- [ ] Prove tier nesting and old-to-new agreement as theorems (only sampled so far); audit termination, fuel, stack safety and protocol-scale resources. **The termination/fuel audit is the item that could invalidate the approach and is not started** — raising the cap 290× makes executions reachable that previously never ran.

Evidence: [L1 log](../logs/lean-chunk-L1-2026-10-23.md). The larger bound alone does not close this lane.

Start: `NearSpecV3/ChallengeChunkV3.lean`, `D3/FunctionCall.lean`, `Scope` research definitions,
`formal-core/ArenaCore/Admission.lean` and candidate model/certificate patterns.

Deliver an additive successor relation/checker and tier predicates. Separate protocol semantics
from candidate resource budgets. Replace the proof-capacity-derived gas restriction with protocol
behaviour, preserving the old signed definitions unchanged. A larger numeric cap alone is insufficient:
audit evaluator termination, fuel, stack safety and full-size resource use.

Acceptance: prove the successor checker characterizes its relation; prove each new tier's inclusion
in that relation and the declared nesting between tiers. Prove old-to-new agreement on overlapping
domains or document an actual semantic correction with counterexample and successor-only migration.
Pass tests below, at and above old `G_α`, plus protocol gas limits and overflow/out-of-gas paths.
No prover-specific AIR, commitment or recursion implementation may be required by the semantic API.

### L2 — floating-point Wasm

**Progress through `e34852568`:**

- [x] Merged pure Lean bit-pattern semantics for all **70 no-immediate float opcodes**, plus constants, loads/stores, preparation, validation and gas analysis; additive `checkD3F` and protocol-gas composition (`2816a0882`).
- [x] Added **141 kernel-checked tests**. Recorded nearcore checks cover 1,260 operator cases, 210 gas modules and 140 prepared-module sizes with zero disagreements.
- [x] Completed the recorded **115,284-case D3 replay**: zero baseline regressions, 125 expected float-domain moves, zero unexpected moves. Focused whole-chunk tests lifted 20 cases and rejected 80/80 tampered inputs.
- [ ] Expand generated whole-chunk coverage beyond the single `d3float` contract; prove chunk-level overlap agreement (currently tested, with guard-level agreement proved).

Evidence: [L2 log](../logs/lean-chunk-L2-2026-10-23.md). Lean-to-nearcore agreement is testing, not a refinement theorem.

Deliver all target-accepted f32/f64 operations, conversions, comparisons, reinterpretations and
preparation rules with exact pinned NaN, rounding and trap behaviour.

Acceptance: coverage includes every opcode; test signed zero, subnormals, infinities, NaNs/payloads,
rounding ties, conversion boundaries and traps. Distinguish operations that canonicalize NaNs from
bit-preserving operations. Test gas and outcomes through full chunks, not just isolated arithmetic.
No native floating-point shortcut may bypass the certified executable semantics.

### L3 — cryptographic and key coverage

**Progress through `e34852568`:**

- [x] Merged `ecrecover` and `p256_verify` arithmetic and additive host implementations, source inventory and directed tests (`51ddfaff1`). Integration reran 161 ecrecover vectors, 20 edge and 23 host cases, plus 17 p256 vector/gate and 13 host cases, with zero failures.
- [ ] Wire these hosts into a successor accepted chunk path and validate valid/invalid whole chunks; implement remaining crypto/key families and their required generated/boundary tests. Both implemented host families remain **partial** in the inventory.

Evidence: [L3 log](../logs/lean-chunk-L3-2026-10-23.md).

Inventory actual missing paths before implementation: curve hosts (`ecrecover`, `ed25519_verify`,
`p256_verify`, `alt_bn128_*`, `bls12381_*`), secp256k1 transactions/delegates and ML-DSA key/signature
variants. Existing Ed25519 transaction support does not imply its host path is complete.

Acceptance: executable trusted-path implementations; positive/negative algorithm vectors; malformed
encodings, invalid signatures, noncanonical scalars, subgroup/infinity cases and PV86-specific quirks;
exact host gas and return/error behaviour; at least one valid and invalid whole-chunk case per supported
entry path. No verifier-result oracle or “signature valid” hypothesis substitutes for checking it.

### L4 — missing actions, hosts and contract resolution

**Integration update — 2026-10-24 (L4 through `06dffaac6`):**

- [x] Merged additive global-contract/state-init codecs, resolution, fees and action bodies for tags 9/10/11, with 134 kernel-evaluated directed tests.
- [x] Merged `functionCallResolved`/`resolveAccount`, `checkD3Global`/`RelD3Global`, and guard-premise gap theorems.
- [x] Recorded 539 excluded-case comparisons with unchanged verdicts/reasons; five inventory rows move missing → partial. This is preservation evidence, not newly accepted semantics.
- [ ] Connect widened action/receipt codecs and dispatch through W00's versioned successor; the current checker still calls D2 decoders and rejects tags 9/10/11.
- [ ] Implement successor ETH-local handling: rewriting the contract to local preserves the old rejection guard.
- [ ] Generate positive global/by-account/wallet whole chunks using versioned successor tooling while preserving the pinned oracle. Validate fees, receipts, rollback, cache and resolution.
- [ ] Resolve UQ-006 against source-proof reachability. Non-instant distribution receipts alone do not establish impossibility; the lane's exclusion claim is not accepted as closure.

Evidence: [L4 handoff log](../logs/lean-chunk-L4-2026-10-23.md), [integration record](../logs/lean-chunk-integration-2026-10-23.md), [action module](../../spec/lean/v3/NearSpecV3/D3/GlobalContractExec.lean), [successor hook](../../spec/lean/v3/NearSpecV3/D3/GlobalContractCall.lean), [successor checker](../../spec/lean/v3/NearSpecV3/D3/GlobalContractChunk.lean), [replay evidence](../../evidence/lean-chunk-L4/replay/d3-hook-full-replay-summary.json).

Cover global-contract deployment/use/distribution, deterministic state-init actions, excluded gas-key
and related host paths, ETH-implicit wallet execution, and code deployment/cache/preparation cases.
L0 determines the exact reachable list; host imports alone do not establish executed coverage.

Acceptance: exact codecs, fees, receipts, state writes and rollback behaviour for every added variant;
success and failure exercised through a real chunk. Cache-sensitive cases require a defined validator
environment or a justified deterministic boundary, not an undocumented cold-cache assumption.
Test same-chunk deploy/call, rolled-back deploy, postponed calls and missing code blobs.

### L5 — storage accounting and protocol resource boundaries

**Progress through `e34852568`:**

- [x] Merged storage-bound analysis and kernel-checked facts distinguishing the conservative witness bound from protocol per-receipt limits (`a98bd9965`).
- [ ] Implement actual accounting/exhaustion semantics and validate below/at/above-limit cases, rollback, exact gas/roots and resource use. The existing exclusion has not been removed.

Evidence: [L5 log](../logs/lean-chunk-L5-2026-10-23.md).

Replace conservative witness restrictions that avoid storage-proof exhaustion with actual accounting
and failure semantics. Audit trie read caching, writes/removals, rollback, code reads and implicit
transitions. Preserve protocol limits rather than simply deleting checks.

Acceptance: boundary cases below/at/above every applicable limit, repeated reads, deleted/reinserted
keys, shared paths, large code and receipt rollback; exact gas, outcomes and roots match the pinned
validator. Test the source-documented uncertainty about recorded-storage upper bounds explicitly.
Record maximum supported fixture runtime/memory for judge budgeting; resource failure is not validity.

### L6 — resharding and remaining validator boundary cases

**Progress through `e34852568`:**

- [x] **The genesis-checker soundness correction is merged and validated.** The draft checker re-implemented the non-genesis tail and dropped ten endorsed-header comparisons, wrongly accepting 307 header mutants; `checkD2CoreG` now delegates to `checkD2Core` for `!B2.isGenesis`. Measured over the full replay: **exactly 137 verdicts change, all `out_of_domain → accept`, all genesis; zero non-genesis changes across 115,147 cases.** 137/137 genesis cases accept and 16 directed negatives fire their intended checks. The genesis branch is additive: signed `checkD2Core`/`checkD3` are unchanged.
- [ ] Deliver actual resharding/split transitions and validator-generated boundary fixtures; the boundary analysis alone does not implement them. The two guards are stated and their exclusion argument proved (`sameLayout_forbids_resharding`, `noSplitGate_iff` + `splitGate_excludes_nonempty`), but `ImplicitTransitionParams::Resharding` itself remains unimplemented and the split gate **is** reachable at PV86 on mainnet.

Evidence: corrected [genesis checker](../../spec/lean/v3/NearSpecV3/GenesisD3.lean), [resharding analysis](../../spec/lean/v3/NearSpecV3/ReshardingD3.lean) and current [inventory](../research/lean-chunk-coverage.json). The earlier [holdback record](../logs/lean-chunk-integration-2026-10-23.md) is historical; `bcbfd97f1` was merged through `4d4fd40c3`.

Deliver shard-layout transitions, split gates, resharding witness processing and any genesis/segment
paths L0 establishes as reachable. Extend the successor claim format only when required, documenting
how each added fact is authenticated and why the existing format cannot express it.

Acceptance: validator-generated fixtures cross a real layout boundary and exercise split/no-split,
nonempty state and outgoing buffers, applicable epoch updates, corrupted witness/root/layout/fact
negatives. Compare all intermediate roots and final outputs. No blanket same-layout exclusion remains.

### L7 — differential validation and integration

**Progress through `e34852568`:**

- [x] Merged corpus manifests, verification tooling, measured regression evidence and readiness assessment (`0cf6f3491`); integration verified all 18 manifest families and reran 28 harness self-tests.
- [x] Recorded validation gaps, including the UQ-014 engine `LoadingError` divergence, rather than treating them as passed coverage.
- [x] Audit and harness updates committed and merged: UQ-014 answered per branch, readiness assessment, two new oracle test scripts.
- [x] **Added CI wiring** (`difftest-gates` job) for 28 harness self-tests and the corpus-manifest check. `spec/lean/v3` is also now in the CI Lean matrix and `make lean`.
- [ ] Make the manifest CI job executable on its runner: `corpus_manifest.py --verify` requires the pinned corpora, which the current hosted job does not provision. Add explicit build coverage for successor modules/drivers outside the default root; see completion-workplan W01.
- [ ] Complete per-family generated whole-chunk coverage, observable comparisons, all unresolved disagreements and the 1,000-consecutive-block/all-shard validator-witness replay. The full 115,284-case differential sweep still needs the pinned corpora and remains a local/integration step.

Evidence: [L7 log](../logs/lean-chunk-L7-2026-10-23.md), [readiness assessment](../evidence/lean-chunk-L7/readiness-assessment.md).

Own the common harness, fixtures, coverage reports and combined regressions in §5. Help each lane
obtain independently generated nearcore outcomes. Do not repair disagreements by relaxing comparisons
or allowing formerly valid cases to become unsupported.

Acceptance: reproducible corpus manifests, complete machine-readable output, documented oracle
provenance, zero unexplained differences, and explicit reachability of every inventory row marked
validated. A percentage of module coverage is not a substitute for semantic-path coverage.

### L8 — reference admission and arena release

**Progress through `e34852568`:**

- [ ] No additional committed L8 checkpoint was available at integration. Verify artifact-bound live admission evidence for Gate A; successor packaging and Gate C remain open.

Evidence: [integration record](../logs/lean-chunk-integration-2026-10-23.md). Historical admission/deployment evidence in §2 is not a new certification.

Can start Gate A now. Inspect existing reports before repeating completed expensive checks.
After semantic integration, package the successor reference and complete Gate C.

Acceptance: exact package passes all configured formal/runtime gates and is ADMITTED live; signed
report and reproducible build digests agree; public contributor instructions work from a clean
checkout; excluded cases are classified separately from invalid cases; tiers and scoring cannot
reward an implementation for abstaining on required inputs. Include verifier-side attacks, not just
proof-generator refusals. Never publish held-out cases or seeds.

## 5. Validation required for every semantic extension

1. **Target identity:** record source commits, compiler/toolchain versions, runtime parameters,
   oracle build recipe, executable hashes and commands in a manifest.
2. **Directed tests:** cover every added dispatch branch and protocol boundary with a positive
   execution where possible and a discriminating negative. Run at least one regression experiment
   showing removal/breakage of the new behaviour makes a targeted test fail.
3. **Generated tests:** at least 1,000 generated comparisons per new semantic family across at least
   four recorded seeds, in addition to directed cases. Use reduced, minimal reproducible cases for
   failures. This is a minimum test budget, not a proof of completeness.
4. **Chunk integration:** exercise each new family through the whole checker with honest validator
   witnesses and tampered claims/witnesses. Compare acceptance and, for executed cases, state roots,
   outcome roots, gas/compute, refunds, logs, return data and emitted receipts. Respect the existing
   error-kind quotient; exact error strings are not an acceptance requirement.
5. **Regression:** reproduce existing D1/D2/D3 regression corpora, including the recorded 53,048,
   67,384 and 115,284-case suites where available. Record content hashes, not just counts. If a corpus
   cannot be recovered, regenerate from its pinned recipe and document the evidence replacement;
   do not call it an exact replay. No previously accepted unchanged-domain case may silently regress.
6. **Representative replay:** before Gate B, execute validator witnesses for at least 1,000 consecutive
   blocks across all shards in a recorded PV86 window. Also run targeted fixtures for rare branches
   absent in that window. Metadata-only workload classification does not satisfy this gate.
7. **Formal checks:** build the actual changed declaration closure from a clean checkout; check all
   new theorems' transitive axioms and runtime-path restrictions. Standard allowed logical axioms
   remain `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, new axioms or native shortcuts.
   A theorem still requiring the missing semantic result as a premise is not closure evidence.

Cryptographic algorithm conformance and Lean-to-nearcore testing must be labelled as testing.
Kernel proofs of checker equivalence, normalization, inclusion and artifact binding must be labelled
as proofs. Full formal refinement of nearcore is a separate project, not an implicit completion claim.

## 6. Dependencies and execution order

1. Start L0 and L8's existing D3α admission audit. Establish the coverage inventory before claiming
   an estimate for full completion. Other lanes may inspect/test known gaps while L0 runs.
2. L1 establishes the additive successor API. L2–L5 develop against that API in isolated worktrees;
   L3 may be split by algorithm family with a shared codec/host owner.
3. L6 starts after L0 settles validator/claim boundaries; it need not wait for floats or crypto.
4. L7 runs continuously and gates every integration. Use one integration owner for shared hook,
   codec, relation and root-import edits.
5. Close Gate B only after all L0 inventory rows are accounted for. L8 then performs the final
   freeze, clean admission and authorized release sequence for Gate C.

No duration is committed here: L0 must produce per-family estimates grounded in missing source
paths, fixtures and proof obligations. AIR/PQ lane estimates must not be reused as semantic estimates.

## 7. Agent handoff and integration rules

Each lane must leave `docs/logs/lean-chunk-LN-YYYY-MM-DD.md` containing:

* Owner, worktree, branch, base commit and exact committed tip; state whether merged or pending.
* Inventory IDs owned, implemented behaviour, remaining gaps and dependencies.
* Changed declarations and precise theorem statements, including every residual premise.
* Build/test commands, artifact hashes, actual counts, failing cases and evidence paths.
* Next executable step and files safe for the next agent to edit.

Work in a lane worktree, not the main checkout. Never hard-link `.lake` caches. New modules must be
reachable from the intended root build and have fresh compiled artifacts. Rebuild executables after
semantic changes; mtime alone is insufficient identity evidence. Run `make pin-check` on integration.
Run relevant Rust formatting/lint/test gates when changing Rust, and the actual arena formal checker
on release packages. Push checkpoints according to repository policy; never overwrite another lane's
uncommitted work. Keep logs in `docs/logs/` and link the current plan from the handover at integration.

### Completion record

| Gate | Status through `e34852568` | Required evidence owner |
|---|---|---|
| A restricted research arena | Open / not newly certified; prior evidence still requires exact-package live admission verification | L8 |
| B full executable PV86 transition | Open; merged partial progress above, semantic exclusions and validation obligations remain; corrected genesis merged, actual resharding still missing | L0 plus L1–L7 |
| C full transition arena release | Blocked on B and successor admission | L8/integration owner |

Closing a gate requires links to the exact evidence above and a recorded release/commit identity.
A clean lane, a green root build or a newly stated theorem is not by itself a completion record.
