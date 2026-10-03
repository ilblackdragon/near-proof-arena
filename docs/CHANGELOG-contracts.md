# Contract changelog

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
