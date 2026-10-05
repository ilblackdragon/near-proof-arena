# Untrusted NEAR ZK implementation: correctness audit and agent handoff

Date: 2026-10-05

Audited revision: `8e831a6` (the HEAD inspected during the audit).

This report records the preceding audit, not a certification of the repository. HEAD had advanced to `5d6961e660758da6ca263d62483a591d783b7ec3` when this report was saved. The implementing agent must check subsequent changes before treating a finding as still open. No implementation changes were made by the audit.

**Post-audit update:** the intervening history includes `5fa43e9` (merge of the candidate `@[csimp]`/candidate-wide axiom audit fix) and `5d6961e` (documentation reporting M2 passing under the fixed checker and the R-L7-5 reproducer failing with `SORRY_FOUND`). Treat A01 below as a historical finding with a reported fix pending independent verification, not as a confirmed vulnerability in the new HEAD. Review that patch, rerun its regression tests, and check cache invalidation before doing duplicate implementation work. The other findings were not re-audited against the new HEAD.

## Conclusion

At the audited revision, the repository was not ready for end-to-end verification of an untrusted NEAR ZK implementation. There is substantial formal infrastructure and a closed toy STARK admission theorem, but a critical native-verifier audit gap and missing NEAR integration prevent that conclusion.

The intended security chain is:

1. Authenticate the chain context and transition inputs, if claiming an actual on-chain transition.
2. Define the intended NEAR transition relation and its precise scope.
3. Prove that the concrete AIR represents that relation.
4. Prove soundness of the proof protocol at all accepted parameters.
5. Bind that proof to the parser, verifier model, parameters, and exact executed artifact.
6. Run the untrusted package through mandatory isolation, conformance, adversarial, and formal checks.

Testing supplements these links; passing fixtures or proof mutations cannot replace a missing soundness or implementation-connection proof.

## Findings and remediation

### A01 — Critical: unaudited compiler rewrites can change the native verifier

Status at save time: **reported fixed after the audited revision; verify the fix and cache handling** (see post-audit update above).

**Evidence:**

- [Rust model-closure audit](../runners/formal-checker/src/audit.rs), approximately line 410: `cand.closure([m.model_decl.to_string()])`.
- [Lean model-closure audit](../runners/formal-checker/lean/ArenaAudit/ArenaAudit/Audit.lean), approximately line 244: `closure env #[modelName]`.
- [Native build](../runners/formal-checker/src/pipeline.rs), `native_build`.
- [Source scan](../runners/formal-checker/src/grep.rs): supplementary warnings do not decide gates.
- Existing full-checker reproduction: [R-L7-5](zk-formal/REQUESTS.md), approximately line 338.

Both audits root the model closure at its constant, omitting candidate `@[csimp]` compiler-rewrite lemmas. A rewrite can redirect compiled execution without becoming a logical dependency of the model or its certificate. Checking the certificate and hashing the judge-built executable does not close this gap.

The repository's R-L7-5 records a full checker run in which all formal gates, including AXIOM_AUDIT and ARTIFACT_BINDING, pass, while the judge-built verifier accepts garbage after a `sorry`-backed rewrite. That full run was not independently repeated during this audit.

The underlying mechanism **was independently reproduced** with the following scratch file:

```lean
import Init
namespace AuditCsimp
def verified (x : Nat) : Bool := x == 7
def replacement (_ : Nat) : Bool := true
@[csimp] theorem redirect : @verified = @replacement := sorry
theorem verified_rejects_garbage : verified 99 = false := by decide
#print axioms verified_rejects_garbage
#print axioms redirect
end AuditCsimp
def main : IO Unit := IO.println (AuditCsimp.verified 99)
```

Running `lake env lean --run /tmp/nearproof-audit-csimp.lean` from `formal-core` printed:

```text
'AuditCsimp.verified_rejects_garbage' does not depend on any axioms
'AuditCsimp.redirect' depends on axioms: [sorryAx]
true
```

**Remediation:** audit and independently recheck the compiler-rewrite dependency closure used by the native build, or reject candidate rewrites until that support exists. R-L7-5 suggests enumerating candidate entries in `Lean.Compiler.CSimp.ext` as additional audit roots. Cover the Lean and exported-environment audit paths and ensure compiler dependencies are exported/rechecked. Review other compiler-affecting attributes under the same threat model. Version/invalidate affected formal-result caches; assess prior native-route admissions.

**Acceptance criteria:**

- Add the malicious rewrite to native-route regression tests; it must fail with `SORRY_FOUND` or an explicit unsupported-rewrite rejection.
- Repeat the full checker reproduction against the fixed checker.
- Legitimate proved rewrite lemmas either pass after complete auditing or are explicitly disallowed by policy.
- Cached results produced by the vulnerable checker cannot substitute for a new check.

An accept-all example may be caught by the adversarial suite. This does not restore the missing universal implementation-connection guarantee.

### A02 — Blocker: the concrete NEAR AIR and packaged STARK certificate are missing

**Evidence:**

- [NEAR assembly](../zk-formal/ZkFormal/NearAssembly/Certificate.lean): `near_admission` requires `L6Facts A honestTrace`.
- [Packaged prover](../examples/np-udr-stark/source/src/bin/prove.rs): exits with `not yet implemented: NEAR AIR pending (L6)`.
- [Packaged verifier model](../examples/np-udr-stark/formal/NpUdrStark/Model.lean): reject-all placeholder.
- [Package manifest](../examples/np-udr-stark/candidate.toml): names the planned `NpUdrStark.certificate` and an older challenge.

`L6Facts` contains the essential obligations: AIR soundness and completeness for `NearRelation`, honest-trace header validity, nonempty/bounded table count, proof-size bound, verifier query budget, and `NpOk`. A theorem conditional on this structure is not a completed NEAR certificate.

**Remediation:** implement the concrete NEAR AIR and witness-to-trace generator; discharge every `L6Facts` field; replace the packaged placeholder model; implement the judge prover entry point; package a closed certificate against a compatible frozen challenge. Ensure vendored formal sources, generated AIR data, and challenge/template pins agree.

**Acceptance criteria:**

- A concrete closed NEAR admission certificate checks without added axioms, `sorry`, or extra unproved hypotheses.
- Judge `prove` produces valid claims/proofs from NEAR fixtures and sampled cases.
- The exact judge-built verifier accepts honest proofs and rejects false claims/malformed proofs.
- A complete formal-tier pipeline run produces all mandatory passing gates and an artifact-bound report.

### A03 — Mainnet blocker: statement scope and chain authentication are incomplete

**Evidence:**

- [V1 relation](../spec/lean/NearSpec/TransferV1.lean), `NearRelation`.
- [V1 scope](../spec/near-transfer-receipt-v1.md): Transfer-receipt slice, projected `slice_post_root`, external chain anchoring.
- [V2 scope](../spec/near-transfer-receipt-v2.md): actual runtime post-state root for a restricted single-shard transition; explicitly excludes current mainnet multi-shard behavior.
- [Historical replay limitations](HISTORICAL_REPLAY.md).

V1 binds a receipt batch and pre-state witness to supplied commitments, but does not establish that they belong to a finalized block. Its output is a slice projection. V2 adds the bandwidth-scheduler write for a restricted single-shard domain, not full mainnet execution. Authentic but rebased historical fixtures are not exact on-chain transition verification.

**Remediation:** explicitly choose the target scope. For actual chain transitions, authenticate headers, pre-state roots, receipt inclusion/order, shard layout, protocol/configuration selection, and finality, either within the proof or in a specified trusted verification layer. Extend transition semantics for the target domain, including multi-shard behavior if targeting mainnet. Maintain the distinction between tested nearcore/spec agreement and a proved refinement.

**Acceptance criteria:**

- The claim and verifier contract state exactly which chain facts are proved, externally authenticated, or assumed.
- Out-of-scope transitions are rejected rather than represented as fully verified NEAR transitions.
- Exact, non-rebased replay compares authenticated pre/post roots and relevant outcomes to the pinned runtime for the chosen domain.
- Broader mainnet claims are withheld until corresponding semantics and authentication are implemented.

### A04 — High: v2 is not integrated into worker oracle selection

**Evidence:** [worker oracle](../runners/worker/src/oracle.rs): `NearOracle::format()` returns only `near-arena-claim-v1`; registry lookup matches the format exactly.

A v2 relation, standalone oracle path, and checker configuration exist, but the inspected worker implementation has no matching v2 oracle registration. A v2 challenge therefore cannot complete conformance through this route.

**Remediation:** wire the v2 oracle route, approved parameters, request pin checks, generator configuration, fixtures, and all dependent stages into the worker. Do not assume standalone differential tests establish pipeline integration.

**Acceptance criteria:** run a v2 challenge through the actual worker pipeline, showing the correct v2 oracle and fixture pins, and rejection of wrong-version requests/claims.

### A05 — Privacy blocker: zero knowledge is not yet an admission obligation

**Evidence:**

- [Admission theorem](../formal-core/ArenaCore/Admission.lean): `Obligations` covers semantics, verifier completeness, and cryptographic soundness; no zero-knowledge predicate.
- [Worker formal gates](../runners/worker/src/stages/formal.rs): a required unsupported `FormalZk` becomes `Unknown`; validity-only challenges can mark it not applicable.
- [STARK manifest](../examples/np-udr-stark/candidate.toml): requests `validity-classical-128`.

The worker is appropriately fail-closed for a required ZK gate. However, a validity admission does not establish witness privacy.

**Remediation:** if privacy is required, define the privacy game/property, implement the necessary prover protections, bind the relevant implementation to the claim, and prove the property. If the goal is succinct validity alone, describe it explicitly and keep this separate from validity blockers.

**Acceptance criteria:** privacy claims require a closed privacy theorem and implemented gate; validity-only admissions are never presented as zero-knowledge guarantees.

### A06 — Medium: committed conformance coverage can be skipped and sampling is predictable

**Evidence:**

- [Worker oracle](../runners/worker/src/oracle.rs): `fixtures_for` returns `None` for an unavailable pinned directory; `conformance_cases` then starts with an empty fixture list and adds generated cases.
- [Seed inputs](../runners/worker/src/executor.rs), `seed_parts`: challenge ID and package digest.
- [Sampling](../runners/worker/src/oracle.rs): derives workload seeds from public inputs; the season-secret HMAC is documented as unwired.

With generated cases available, conformance can pass without exercising the challenge's committed public fixture set. The sampled cases are deterministic from public inputs and do not supply a secret held-out test set.

**Remediation:** fail closed when required fixture sets are unavailable; enforce required dataset/class counts; wire in committed held-out cases or judge-secret sampling with appropriate reproducibility and disclosure controls.

**Acceptance criteria:** missing fixtures and insufficient coverage cannot produce PASS; tests establish the intended sampling/held-out policy. Preserve the distinction between empirical coverage and formal soundness.

### A07 — Medium: CI does not require the complete verification path

**Evidence:**

- [CI workflow](../.github/workflows/ci.yml): Lean matrix includes `formal-core` and `spec/lean`, but not `zk-formal`.
- [Formal worker tests](../runners/worker/tests/formal.rs) and [NEAR worker tests](../runners/worker/tests/near.rs): environment-gated tests can return successfully without exercising formal/Firecracker execution.

**Remediation:** add mandatory STARK builds and certificate rechecks; include native compiler-rewrite hostile cases; run the real pipeline on a KVM-capable runner. Required verification jobs must fail or be explicitly reported as unexecuted when prerequisites are missing, rather than appearing as executed successes.

**Acceptance criteria:** CI demonstrates that the relevant ZK/formal targets and a genuine isolated E2E run executed; negative controls fail at their intended gates.

## Verified progress and retained trust boundaries

- The README/evidence matrix's older “design only” description understates current STARK progress. `ZkFormal.Toy.toy_admission` is closed apart from judge-supplied literals/profile facts.
- `ZkFormal.NearAssembly.near_admission` builds, but remains conditional on `L6Facts`.
- The current Lean STARK verifier enforces `minQueryLog = 8`; the Rust protocol implementation has the corresponding floor. Older notes about accepting smaller query domains should not be reported as a current unfixed bug without checking the code.
- The formal/experimental distinction is implemented; experimental measurement is not formal admission.
- Even after A01, the native Lean route trusts the compiler/runtime/C toolchain. The NPAI route retains a tested, rather than proved, correspondence between its implementation and Lean interpreter semantics.
- Nearcore-to-spec faithfulness remains an independent obligation; differential tests are evidence, not a refinement proof.

## Validation performed during this audit

Commands and outcomes:

```text
cargo test --locked --offline -p arena-types -p arena-npai -p arena-formal-checker --lib
  31 tests passed (18 arena-types, 13 formal-checker; NPAI lib had 0 tests).

cargo test --locked --offline -p arena-npai --tests
  5 integration tests passed (2 assembler, 3 vectors/CLI).

cd zk-formal
lake build ZkFormal.Toy.Certificate ZkFormal.NearAssembly.Certificate
  Successful (215 jobs, including cached/replayed jobs; not a clean rebuild).
```

Additional scratch-file checks using `lake env lean`:

```lean
import ZkFormal.Toy.Certificate
import ZkFormal.NearAssembly.Certificate
#print axioms ZkFormal.Toy.toy_admission
#print axioms ZkFormal.NearAssembly.near_admission
```

Both reported only `propext`, `Classical.choice`, and `Quot.sound`. This does not discharge explicit theorem hypotheses such as `L6Facts`.

The initial Rust test invocation failed because the configured `sccache` could not operate inside the sandbox; the authorized rerun outside the sandbox passed.

Not performed: a fresh full-checker exploit run, a full Firecracker E2E run, a clean independent recheck of the entire STARK development, or a fresh mainnet replay. Existing repository reports are distinguished above from checks independently run during this audit.

## Suggested implementation order

1. Reconcile this report with changes since `8e831a6`, especially any A01 fix.
2. Close A01 and invalidate vulnerable cached results before relying on native-route admission.
3. Choose and document the intended transition scope; complete A02 for that scope.
4. Wire A04 if targeting v2; repair coverage enforcement in A06.
5. Establish mandatory isolated E2E evidence and CI under A07.
6. Extend chain authentication and semantics under A03 for on-chain/mainnet claims.
7. Implement A05 if zero-knowledge privacy is part of the goal.

Do not mark the task complete solely because Lean builds, the toy certificate passes, a conditional NEAR theorem is axiom-clean, or an experimental benchmark accepts honest proofs. Completion requires a closed certificate for the intended NEAR relation, a sound connection to the exact deployed verifier, and an executed mandatory E2E pipeline with negative controls.

## Remediation status

Updated 2026-10-05 on branch `lane/audit-fixes` (based on `8838e1b`). "Fixed"
means the stated acceptance criteria are met by code and tests in this branch;
it is not an independent re-audit. A01 and A02 are owned by other lanes and
are not covered by this branch.

| finding | status | evidence |
|---|---|---|
| A01 | Fixed upstream (`5fa43e9`, `5d6961e`); not re-done here | CI now runs the native csimp hostile cases (see A07) |
| A02 | Open, in progress in other lanes | none here |
| A03 | Scope statement **done**. Chain authentication and multi-shard semantics remain **open** by design (future v3) | `be002d6`, `a0e8785`, web `daa591b` |
| A04 | **Fixed** for worker integration: v2 runs through the real worker pipeline (DEMO tier, test candidate) | `fda64b2`, `964c958`, `35249de` |
| A05 | Labeling **fixed**: validity-only everywhere. A privacy theorem / `FORMAL_ZK` gate is still **open** (not a current goal) | `daa591b`, `be002d6` |
| A06 | **Fixed** | `fda64b2` |
| A07 | **Fixed** in the workflow definition; the hosted jobs have not run on GitHub yet, and the KVM job needs a self-hosted runner | `ff1b030`, `35249de` |

### A03: statement scope

* `README.md` § "What an admitted proof establishes" and
  `docs/AGENT_CONTRACT.md` §6.1 state the scope:
  * v1: the receipt-batch relation with a projected `slice_post_root` over
    externally supplied (anchored) pre-state root and receipts commitments,
    with the challenge's `excludes` quoted verbatim. It does not cover
    finality, inclusion, an on-chain pre-root, data availability or full
    chunk validation.
  * v2: the real post-state root, but only for a restricted single-shard
    domain.
  * Full stateless-validator equivalence would be a future v3 and is not
    claimed.
* The web challenge page already rendered `semantic_scope.excludes` and
  `restrictions` as "What an admitted proof does NOT establish". It now also
  shows "Validity only, not privacy".
* Out-of-scope transitions are rejected.
  * `nearspec-check` (Lean reference) over `oracle/fixtures/{public,rejection}`
    reports 20 ok and 14 `out_of_domain`, with 0 inconsistent.
  * `nearspec-check --scope v2` over `oracle/fixtures/v2/{public,rejection}`
    reports 25 ok and 18 `out_of_domain`, with 0 inconsistent.
  * The rejection fixtures carry no expected claim, so the worker never
    issues them (`NearOracle::read_cases`).
  * `RequestPin` now pins the request encoding and statement id, the
    protocol version and chain, the expected-claim encoding and statement,
    and `params.bin`, including the runtime-config digest
    (`jobs::tests::v1_and_v2_pins_reject_each_others_cases`). This includes
    the v2 `wrong_protocol_version` rejection fixture.
* Still open: authenticated chain context (headers, receipt inclusion,
  finality, shard layout) and multi-shard semantics. No mainnet transition
  claim is made.

### A04: v2 in the worker

* `NearOracle` is registered separately for `near-arena-claim-v1` and
  `near-arena-claim-v2`.
  * A generator spec must name the oracle's `--scope`, otherwise the job
    fails closed.
  * `ARENA_WORKLOAD_GENERATORS` accepts the v1 and v2 spec dirs.
  * `approved_params` checks `params.bin` against the pin.
* `runners/worker/tests/near_v2.rs::v2_draft_challenge_through_the_worker_pipeline`
  runs an unsigned local TEST copy of
  `challenges/drafts/near-transfer-receipt-v2.draft.json`.
  * Stages: validate, build, conformance, adversarial and benchmark, with
    job tier DEMO, on bwrap-dev.
  * Inputs: `near-arena-oracle --scope v2`, the v2 generator specs and the
    digest-pinned `oracle/fixtures/v2/public` (`sha256:074bddfd…`).
  * Result: PASS on 25 fixtures plus 3 sampled cases, with 155 hostile
    inputs rejected.
  * The candidate is the TEST-ONLY `tests/e2e/near-v2-spec-candidate`
    (prove/verify via `nearspec-check --scope v2`). No v2 formal certificate
    exists, so FORMAL_CHECK is not run.
  * The worker only consumes the challenge definition carried by the job, so
    signing was unnecessary and no signed copy was produced.
* `v2_pipeline_rejects_v1_inputs`:
  * v1 fixtures under the v2 challenge fail with INFRA:
    `request format "near-arena-request-v1", challenge expects "near-arena-request-v2"`.
  * v1 generator specs fail with INFRA (`--scope v1`).
  * `near-arena-claim-v3` stays UNKNOWN.
* Unit tests: `oracle::tests::near_v1_and_v2_oracles_are_distinct` and
  `jobs::tests::v1_and_v2_pins_reject_each_others_cases`.
* Gated: `ARENA_NEAR_TESTS=1`, the oracle and `nearspec-check`. It ran
  locally and passed, and it is part of the KVM CI job.
* Not done: a v2 formal (native-lean / STARK) reference candidate. That
  depends on A02-style work for `TransferV2`.

### A05: privacy labeling

* np-udr-stark, SP1 and Plonky3 are described as validity proofs, not
  zero-knowledge, in:
  * `examples/{np-udr-stark,zkvm-sp1,stark-plonky3}/README.md`;
  * `docs/{CONTRACTS,TCB,THREAT_MODEL,PROTOCOL_UPGRADES}.md`;
  * `docs/zk-formal/{DESIGN,STATUS-L7}.md`;
  * `security/README.md`.
* "zk" in `zk-formal`/`ZkFormal` is noted as historical in
  `zk-formal/README.md` and `docs/zk-formal/DESIGN.md`.
* `README.md` and `AGENT_CONTRACT.md` state that formal admission under
  `validity-classical-128` establishes validity only.
* No challenge requires `FORMAL_ZK`, and no part of the formal checker
  produces it.

### A06: coverage and sampling

Fail-closed coverage (`runners/worker/src/oracle.rs`,
`Oracles::conformance_suite`):

* A pinned `public_fixtures` the worker cannot supply is an INFRA error
  naming the pin. Only an all-zero digest means "no fixtures".
* The pinned set must contain an in-domain case.
* Every workload class contributes at least `max(1, ceil(samples/classes))`
  sampled cases.
* Benchmark batches must be full size.
* Every case is pin-checked before any candidate code runs.

Judge-secret sampling (`SeedCtx`):

* With `ARENA_SEASON_SECRET_FILE` (hex, mode 0600, never sandboxed or
  logged), seeds are `HMAC-SHA256(secret, "near-arena-workload-sample-v1|" ‖
  challenge_id ‖ "|" ‖ package_digest ‖ "|" ‖ class)`.
* These seeds are bit-identical to `arena_bench.seeds.derive_sampling_seed`.
* `ARENA_SEASON_SECRET_COMMIT` checks the file against the published
  commit-reveal digest `sha256("near-arena-secret-commit-v1\0" ‖ secret)`.
  Summaries name the commitment.
* Without a secret, summaries say "PUBLIC sampling seeds".
* The procedure is documented in `docs/BENCHMARK_SPEC.md` §11.1–11.3.

Committed held-out sets:

* Held-out sets live in `ARENA_HELDOUT_DIRS` (judge-only), are matched to
  `heldout_commitment` by TreeDigest and are re-hashed on use.
* Once a worker has any held-out dir configured, a missing or mismatched
  committed set is INFRA.
* Conformance uses a seed-selected subset of each class.
* Held-out ids, sizes and failure details are withheld from summaries
  (RT-04).
* A worker without held-out dirs reports "NOT exercised" rather than
  skipping silently.

Tests:

* `oracle::tests::missing_pinned_fixtures_fail_closed`
* `oracle::tests::insufficient_class_coverage_fails_closed`
* `oracle::tests::heldout_set_is_verified_against_the_commitment`
* `oracle::tests::judge_secret_sampling_seeds`: Python reference vectors,
  and seeds change with the secret
* `oracle::tests::season_secret_file_is_judge_only_and_never_printed`
* `pipeline::conformance_fails_closed_without_pinned_fixtures`
* `pipeline::conformance_uses_verified_heldout_set`

Deployment note: the live worker (`deploy/live/arena-live`) has neither a
season secret nor held-out dirs configured. Its runs therefore report public
seeds and "held-out NOT exercised" until the operator sets them. See
`deploy/hardened/env/worker.env.example`.

Coverage remains empirical evidence and never substitutes for formal
soundness.

### A07: CI

`.github/workflows/ci.yml` changes:

* `zk-formal` is in the Lean matrix, with `.lake` caches for zk-formal and
  its formal-core and spec/lean path dependencies.
* It builds the Toy and NearAssembly certificates.
* An axiom gate (`zk-formal/test/AdmissionAxioms.lean`) fails on anything
  beyond `propext`/`Classical.choice`/`Quot.sound`, or on `sorryAx`.

`formal-checker` job:

* Runs `corpus`, `native_lean_route` (including the R-L7-5 `csimp_sorry`
  case), `formal_core_toy` and `near_spec` with
  `ARENA_REQUIRE_GATED_TESTS=1`.
* Asserts from the log that every named test ran.

Gated-test skips (`skip_gated!`):

* Gated tests now print `ARENA-TEST-SKIPPED: <test>: <reason>` instead of
  passing silently.
* Under `ARENA_REQUIRE_GATED_TESTS=1` a skip panics.
* This applies to the worker, formal-checker and firecracker test crates.

`firecracker-e2e` job:

* Runs on `[self-hosted, linux, x64, kvm]`, gated by
  `vars.ARENA_KVM_RUNNER == 'true'` and excluded for fork PRs.
* Runs the real Firecracker E2E (including `near` and `near_v2`) with every
  gate variable set, and asserts that each named test ran.

Validation and gaps:

* actionlint 1.7.12 and shellcheck are clean. zizmor 1.24.1 reports no
  findings (1 suppressed: `self-hosted-runner`, expected).
* The formal-checker gated tests passed locally (corpus 83 s, formal_core
  145 s, native route 64 s, near_spec 35 s).
* Not yet observed: a run of the new jobs on GitHub-hosted runners, and any
  KVM run, since no self-hosted runner is registered.

Workspace checks on this branch:

* `cargo fmt --all --check` and
  `cargo clippy --workspace --all-targets -D warnings` are clean.
* `cargo test --workspace`: 337 passed. `fork_bomb_and_background_daemon`
  failed once from host thread exhaustion (EAGAIN) under full-workspace
  parallelism and passed on two isolated reruns. That flakiness predates
  this branch.
