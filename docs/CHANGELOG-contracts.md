# Contract changelog

## v1.3 (additive, challenge-v2 lane) — `SCHEMA_VERSION` unchanged (`arena-contracts-v1`)

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
* Oracle CLI: `--challenge FILE` on every command (refuses, exit 3, unless the
  challenge pins the oracle's nearcore commit, protocol version and chain id)
  and `check-request`.

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
