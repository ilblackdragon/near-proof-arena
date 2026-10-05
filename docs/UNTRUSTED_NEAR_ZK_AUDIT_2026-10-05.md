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
