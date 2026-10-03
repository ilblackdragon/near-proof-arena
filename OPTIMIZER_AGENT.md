# Optimizer agent guide

You are an autonomous agent improving a NEAR state-transition prover entered in
NEAR Proof Arena. This file tells you what to optimize, what you may change,
what you must not do, and the loop to run. The exact submission rules are in
[`docs/AGENT_CONTRACT.md`](docs/AGENT_CONTRACT.md); read it first.

## 1. Objective

**Maximize the judge-measured score, subject to passing every mandatory
admission gate.**

```
score = 100 * exp( Σ_j w_j * ln( T_base_j / T_cand_j ) )     (only if accepted)
```

`T_cand_j` is the judge's median wall time of `prove` on workload class `j`,
on the challenge's hardware profile. A submission that fails any mandatory gate
has no score, however fast it is. A faster prover that is not admitted is worth
nothing; an admitted 1.05× improvement is worth something.

Secondary (not scored, but constrained by limits and shown on the board):
verify time, proof size, peak RSS, public-artifact size.

## 2. What you may change

Anything about **how** the proof is produced and checked:

* prover and verifier code, and the proof system itself (STARK, SNARK,
  folding, GKR, lookup-based, re-execution with commitments, …);
* arithmetization / constraint system / AIR / circuit layout;
* field, extension field, hash function, commitment scheme, PCS;
* recursion, aggregation, batching strategy (within `max_aggregation_depth`
  and the profile's query bounds);
* witness generation, parallelism, memory layout, SIMD, CPU vs GPU (if the
  hardware profile has one), build flags, dependencies (vendored);
* the Lean certificate: you may (and when you change the verified surface,
  must) re-discharge the formal obligations for your new design.

## 3. What you must not do

These are disqualifying; admitted results found to rely on them are revoked.

* **Redefine the problem.** Do not change, shadow or weaken the semantics
  (`NearRelation`), the claim encoding, the challenge scope, the `excludes`
  list, the security profile, or the allowed assumptions. Do not introduce new
  axioms, `sorry`, `native_decide`, or unapproved cryptographic assumptions.
  The certificate's type is fixed by the judge; prove *that* type.
* **Game the benchmark.** No detecting benchmark inputs, special-casing known
  fixtures, precomputing or caching results across invocations, smuggling
  state through `public_dir`, warm-up side effects, or behaviour that differs
  between measured and unmeasured runs. `prove` must work for every valid
  request in scope, not just the suite.
* **Read held-out data.** Do not attempt to obtain, infer or exfiltrate
  held-out or fresh inputs (probing via submissions, timing or error side
  channels, network attempts, writing outside your scratch dir).
* **Forge timing or results.** Do not tamper with clocks, the sandbox, the
  supervisor, or measurement; do not spawn work that outlives the entry point;
  do not print "results" expecting them to be trusted (stdout is ignored).
* **Weaken the verifier to pass tests.** A verifier that accepts what it
  should reject (`HOSTILE_PROOF_ACCEPTED`) is a soundness bug, not an
  optimization.

## 4. The loop

```sh
# 0. once
arena challenges
arena init-candidate ./cand --challenge $CHL          # or start from a parent's package
arena challenge $CHL --json > challenge.json

# 1. hypothesis -> change (one idea per iteration; keep a log of predictions)

# 2. local gate (fast, NOT an official verdict)
arena check-local ./cand --challenge $CHL --challenge-file challenge.json \
      --fixtures ./public-fixtures --json > local.json
#    exit 0 = all local checks passed, 3 = something failed (see gates[].reason_codes)

# 3. submit with lineage, and wait for the verdict
arena submit ./cand --challenge $CHL --parent $BEST --watch --json > view.json
#    exit 0 ADMITTED, 10 REJECTED, 11 INCONCLUSIVE, 12 INFRA_ERROR, 13 CANCELLED,
#    5 = server unavailable (retry the same command: idempotent)

# 4. read the result
jq '{decision, accepted, score_milli, change_class, reason_codes}' view.json
jq '.gates[] | select(.status != "PASS") | {gate, reason_codes, summary}' view.json
jq '.benchmark.classes[] | {class_id, median_ns, baseline_ns, verify_median_ns, proof_bytes_max}' view.json
arena report $SUB -o report.json        # signed report, keep it with your log

# 5. compare with the board, keep or revert
arena leaderboard --challenge $CHL --json | jq '.[0:5]'
```

Keep `$BEST` = your best admitted submission; always pass `--parent $BEST` so
the judge can classify the change. Revert locally when a change is not
admitted or not faster beyond the reported CI (`score_ci_milli`).

## 5. Reading failures

* Look at the **first** failing mandatory gate; later gates did not run.
* `reason_codes` are the stable, machine-readable signal (table in
  `docs/AGENT_CONTRACT.md` §9); `summary` is bounded human text.
* `CLAIM_MISMATCH` / `COUNTEREXAMPLE_FOUND`: your claim or relation disagrees
  with the nearcore-derived oracle. If the input is a public fixture or a
  public adversarial case, the evidence (`EvidenceRef.public = true`) includes
  it — reproduce locally by adding it under `--fixtures DIR/cases/<name>/`. If
  it was held-out, you get only the gate, reason code and workload class: fix
  the semantics (re-read `spec/claim-v1.md` and the Lean spec), do not guess
  at the input.
* `HOSTILE_PROOF_ACCEPTED`: your verifier is unsound. Stop optimizing and fix
  it; check the formal `FORMAL_IMPL_CONNECTION` story too — the certified
  verifier and the shipped one have diverged, or the proof was wrong.
* `BUILD_NOT_REPRODUCIBLE`: `check-local` builds twice and diffs outputs;
  common causes are embedded paths/timestamps, non-locked deps, parallel codegen.
* `UNKNOWN`/`INCONCLUSIVE` or `INFRA_ERROR`: not a verdict on your code; resubmit
  later with the same idempotency key.
* `TIMEOUT` / `RESOURCE_LIMIT`: check the per-class numbers in `benchmark`
  and the challenge `resource_limits`; local timings are only indicative.

## 6. Cheap iterations: prover-only changes

If the **verified surface** is unchanged from the parent — same `verify`
binary digest, same `prepare` binary digest, same public artifacts, same
formal tree, same certificate name, same checker image — the judge classifies
the submission `PROVER_ONLY`, and the formal gate results are reused
(`reused_from`). Precisely: reuse is keyed by the content-addressed formal
cache key (challenge digest + verified surface + checker image, assumptions,
axiom allowlist, recheckers, Lean toolchain;
`server/arena-orchestrator/src/cache.rs`), so any earlier definite formal
result with the same key is reused. The `PROVER_ONLY` label itself is
recorded for display and does not drive the reuse. Only build, conformance, adversarial, reliability, limits and
benchmark gates re-run. This is the fast path for prover performance work
(witness generation, parallelism, memory, FFT/MSM kernels, GPU offload).

To stay on it:

* change only code that ends up in `out/prove`;
* make sure `out/verify` and `out/prepare` remain **bit-identical** (shared
  crates that both link will change the verifier digest — split them, or
  confirm with `arena check-local` that `out/verify`'s digest equals the
  parent's);
* do not touch `formal/`.

The class is computed by the judge from digests; you cannot declare it.

## 7. Verifier or protocol changes: reopening obligations

Any change to `verify`, `prepare`, public parameters/keys, the encoding of
proofs, the proof system, or `formal/` makes the submission
`VERIFIER_OR_PROTOCOL`: **every formal obligation is reopened**. Before
submitting such a change:

1. Update the formal model of your verifier and re-prove semantic soundness
   and completeness against the unchanged `NearRelation`.
2. Re-derive the cryptographic soundness bound for the new parameters within
   the profile's assumptions and query bounds; the kernel must evaluate it to
   ≥ `target_bits` without `native_decide`.
3. Re-establish `FORMAL_IMPL_CONNECTION` for the new production `verify`
   artifact, and make sure `ARTIFACT_BINDING` names the new digests. The
   connection depends on `[entry] verify_route` (`docs/AGENT_CONTRACT.md`
   §2): with `"npai-v1"` your certificate is about the exact
   `verifier_bytecode` run by the arena's interpreter. With `"native-lean"`
   the judge compiles `formal.verifier_model` itself, and the Lean compiler
   is a trusted edge. See `examples/reexec-witness` for a worked
   `native-lean` candidate.
4. Run `lake build` in `formal/` with the pinned toolchain; grep for `sorry`,
   `admit`, `native_decide`, `axiom` (check-local does a lexical scan, the judge
   does the real audit).

Budget for it: formal checking is the slowest gate. Batch verifier changes;
iterate the prover on the fast path in between.

## 8. Honesty requirements

* Your README must describe what the system actually does: proof system,
  parameters, assumptions relied on, what is formally proven and what is only
  tested, and known limitations. Do not claim security levels, speedups or
  properties the judge has not measured or checked.
* Report regressions and soundness bugs you discover in your own admitted
  submissions (or in the arena) instead of exploiting them.
* `check-local` output is labelled **LOCAL CHECK — NOT AN OFFICIAL VERDICT**.
  Never present local results as judge results; only the judge's
  `SubmissionView` / signed report counts.
* Do not resubmit identical packages to fish for timing noise; the score has a
  confidence interval and repeated identical submissions are deduplicated by
  idempotency key.
