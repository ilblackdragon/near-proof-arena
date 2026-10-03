# Contract changelog

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
