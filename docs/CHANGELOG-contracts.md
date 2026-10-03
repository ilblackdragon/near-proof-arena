# Contract changelog

## v1.2 (additive, formal-checker lane) — `SCHEMA_VERSION` unchanged

Optional manifest fields (absent = previous behaviour); coordinated with the
spec-oracle lane (`verify_route` / `verifier_bytecode` are shared):

* `[entry] verify_route` ∈ {`"npai-v1"`, `"native-lean"`} and
  `[entry] verifier_bytecode` (required for `npai-v1`).
* `[formal] verifier_model` (e.g. `"Candidate.Model.verify"`, an
  `ArenaCore.OracleVerifier`) and `[formal] verifier_model_module`
  (e.g. `"Candidate.Model"`); required for `native-lean`. The judge splices
  the model into the expected statement (`.nativeTrusted <judge-built binary
  digest> <toolchain id> model`) and builds the `verify` executable itself
  from that model; a candidate-built native verifier is never admitted
  (`ARTIFACT_BINDING_FAILED`). See `runners/formal-checker/README.md`.
* `formal.certificate` is now validated as a dotted Lean identifier.

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
