# Contract changelog

## v1.5 (additive, scoring-v2 lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

Cost-normalized scoring (docs/BENCHMARK_SPEC.md §14). All new fields are
optional or defaulted, and none is serialized when absent, so every existing
challenge id, result and signed report is unchanged.

* `ChallengeDefinition.scoring: Option<ScoringSpec>`
  (`arena_types::scoring`) contains:
  * `kind`: `speed` | `cost_v1`;
  * `price_model`: an `arena-price-model-v1` model, inline;
  * `price_model_digest`: the JCS sha256 of that model, which must match;
  * `cost_baseline`: per class `{class_id, prove_ns, verify_ns, proof_bytes}`,
    where `prove_ns` must equal `workload_suite.baseline_ns`;
  * `cost_baseline_prepare_ns`.

  Absent means `speed`. `ChallengeDefinition::check_scoring` runs in
  `arena-admin verify` and at server registration (`verify_definition`). A
  `formal` challenge must pin a `governed` model.
* `ClassMeasurement.verify_runs_ns` and `proof_bytes_runs`: per measured run,
  Σ verify wall ns and Σ proof bytes of the batch, in the same order as
  `runs_ns`.
* `BenchmarkResult.cost: Option<CostResult>` holds the kind, the price-model
  id and digest, `validators_per_chunk`, `verifier_vcpus`, `score_milli`,
  `score_ci_milli` and per-class `CostClass` (component medians and each
  `*_fusd` term). The server recomputes it from the per-run vectors. It drops
  the result on speed-only challenges and when the vectors are missing.
* `LeaderboardEntry` gains `board`, `cost_score_milli`,
  `cost_score_ci_milli` and `cost`. `GET /v1/leaderboards/{id}?board=cost_v1`
  serves the cost board, or 404 if the challenge has none.
  `arena_db::views::Leaderboard` gains `scoring_kind` and `cost_ranked`.
* Worker: for `cost_v1`, `verify` is pinned to the first
  `price_model.verifier_vcpus` benchmark CPUs (fail closed). The session
  report gains `measured_verify_runs_ns` and `measured_proof_bytes_runs` per
  class.
* Test vectors: `benchmarks/testvectors/cost.json`
  (`arena-bench-cost-testvectors-v1`).

## v1.4 (additive, challenge-v2 lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

Protocol-upgrade governance (docs/PROTOCOL_UPGRADES.md). All new fields are
defaulted (`#[serde(default)]`) or optional and not serialized when absent.

* `LeaderboardEntry` gains `challenge_id: String`, `protocol_version: u32`
  and `superseded_by: Option<String>`: every result is labelled with the
  challenge (and protocol version) it was measured under; a superseded
  challenge's board keeps its ranking and carries the successor id.
* `GET /v1/challenges[/{id}]` (`StoredChallenge`) gains
  `superseded_by: Option<String>` (a registered challenge whose `supersedes`
  names this one).
* Registration policy: registering a challenge whose `supersedes` names a
  registered challenge sets the predecessor `open = false` in the same
  transaction (audit event `challenge.superseded`); a challenge registered
  after its successor is inserted closed. `POST /v1/admin/challenges/{id}/status`
  with `open: true` on a superseded challenge returns 409
  `challenge_superseded`. Submissions to a closed challenge keep returning 409
  `challenge_closed`; the message names the successor.
* Worker jobs (`runners/worker` `ConformanceJob`, `BenchmarkJob`) gain
  `request_pin: Option<RequestPin{format, protocol_version, chain_id}>`
  (`RequestPin::from_challenge`): every oracle request header is checked
  before any candidate code runs; a mismatch fails the job as infra.
* `MeasurementProcedure.invocation_mode: Option<"vm_per_invocation" | "vm_per_batch">`
  (not serialized when absent ⇒ existing challenge ids unchanged; absent =
  `vm_per_invocation`, bench-spec-v1). `vm_per_batch` = bench-spec-v1.1
  (docs/BENCHMARK_SPEC.md §4.4). `arena_sandbox::Sandbox` gains
  `run_steps`/`steps_share_instance` (default impl: one run per step);
  Firecracker guest protocol gains steps mode (`GuestJob.steps`,
  `GuestReport.steps`, `ShimResult.step_wall_ns`, STEP markers; all
  serde-defaulted, `PROTO_VERSION` unchanged; images must be rebuilt to use it).
* Oracle CLI: `--challenge FILE` on every command (refuses, exit 3, unless the
  challenge pins the oracle's nearcore commit, protocol version and chain id)
  and `check-request`.

## v1.3 (additive, red-team lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

* `VerifiedSurface` gains `verify_route`, `verifier_bytecode` (npai-v1:
  digest of the built bytecode image), `verifier_model` and
  `verifier_model_module` (native-lean). All four are optional and are not serialized
  when absent. The server always sets `verify_route` (the effective route,
  `native` by default), so formal-cache keys computed before this change no
  longer match. The result is a cache miss and a re-check, never a false hit.
  Why: these inputs change the judge-built `art.impl`, or the code that runs as
  `verify`. Without them, a child submission that swapped only its NPAI bytecode would hit
  the parent's formal-cache entry and inherit formal PASSes that were never
  checked for its own bytecode (redteam/FINDINGS.md RT-01).
* `arena_jobs::BuildOutputs` gains `verifier_bytecode: Option<Digest>`. A
  passing npai-v1 build that omits it gets no verified surface, and the run
  blocks (fail closed).
* Schemas regenerated (`verified-surface`, `submission`); `server/openapi.json` refreshed.

## v1.2 (additive, spec-oracle lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

All new fields are optional and **not serialized when absent**, so existing
challenge definitions keep their canonical bytes and ids.

* `ChallengeDefinition.formal_params: Option<FormalParams{verify_fuel,
  max_proof_bytes, max_reduction_fuel}>` → `ArenaCore.ChallengeParams.{verifyFuel,
  maxProofBytes, maxReductionFuel}` (docs/FORMAL_INTERFACE.md §2). `arena-admin`
  policy: required for `tier = formal`; `max_proof_bytes` must equal
  `resource_limits.max_proof_bytes`; fuels non-zero.
* `CandidateManifest.entry.verify_route: Option<"native" | "npai-v1">` and
  `entry.verifier_bytecode: Option<path>`; `npai-v1` requires
  `verifier_bytecode`, which must be one of `build.outputs`; a bytecode path
  without `npai-v1` is rejected.
* Governed data (not a schema change): `security/assumptions/*.json`
  `lean_decl` now name the real formal-core declarations
  (`ArenaCore.Assumptions.Sha256CollisionResistant`,
  `ArenaCore.Security.RomSound`) and `lean_decl_digest` is pinned to their
  `decl-hash` (runners/formal-checker `decl-hash` bin,
  `scripts/pin-assumption-digests.sh`).
* Schemas regenerated (`challenge`, `candidate`, `assumption`); `server/openapi.json` refreshed.

### v1.2 addendum (formal-checker lane): native-lean route

* `entry.verify_route` gains `"native-lean"` (`VerifyRoute::NativeLean`).
* `[formal] verifier_model` (e.g. `"Candidate.Model.verify"`, an
  `ArenaCore.OracleVerifier`) and `[formal] verifier_model_module`
  (e.g. `"Candidate.Model"`): required iff `verify_route = "native-lean"`. The
  judge splices the model into the expected statement (`.nativeTrusted
  <judge-built binary digest> <toolchain id> model`) and builds `verify`
  itself from the model; a candidate-built native verifier is never admitted
  (`ARTIFACT_BINDING_FAILED`). See `runners/formal-checker/README.md`.
* `formal.certificate` (and the model names) are validated as dotted Lean identifiers.

## v1.1 (additive, server lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

All new fields are optional/defaulted (`#[serde(default)]`), so v1 producers
and consumers remain compatible.

* `SubmissionView` gains: `artifacts: Vec<ArtifactRef{label, digest}>`,
  `verified_surface: Option<VerifiedSurface>`,
  `build: Option<BuildInfo{toolchain_image?, reproducible, build_ns?}>`,
  `assumptions: Vec<AssumptionRef{id, lean_decl?, description?}>`,
  `trusted_base: Vec<TrustedBaseEntry{id, label, digest?}>`,
  `logs: Vec<LogExcerpt{name, stage, text, truncated}>` (bounded, sanitized
  plain text), `revocation_history: Vec<RevocationEvent{action, reason, at, by}>`.
  Shapes follow `web/README.md` ("API assumptions").
* `LeaderboardEntry` gains `score_ci_milli: Option<u64>`.
