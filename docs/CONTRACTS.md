# NEAR Proof Arena — frozen interface contracts (v1)

This file is the coordination contract for all workstreams. The Rust source of
truth is `common/arena-types` (crate `arena-types`). JSON Schemas under
`common/schemas/` are generated from it (`cargo run -p arena-types --bin gen-schemas`).
Changing anything here is a governed change: bump `SCHEMA_VERSION`, update
both, and note it in `docs/CHANGELOG-contracts.md`.

Final invariant: **candidates control how proofs are produced and checked
internally; the arena controls what must be proved, which assumptions are
allowed, which exact artifacts are certified, and how performance is measured.**

## 1. Identity and hashing

* Digests are `sha256:<64 lowercase hex>` (`Digest`).
* Canonical JSON = RFC 8785 JCS (sorted keys, no insignificant whitespace,
  integers only — no floats in any hashed object; ratios are expressed as
  integer parts-per-million `ppm` or as decimal strings).
* `ChallengeId = "chl_" + hex(sha256(JCS(ChallengeDefinition)))[0..32]`, and the
  full digest is stored too. The definition commits to everything in §2; the
  id is recomputed by every reader and mismatch = reject.
* Artifacts live in a content-addressed store keyed by `Digest` of raw bytes.
  Directory trees are hashed with the `TreeDigest` algorithm: sorted list of
  `(relative_path_utf8, mode in {file,exec}, sha256(content))` serialized as
  JCS array; symlinks, devices, hardlinks, absolute or `..` paths are rejected.

## 2. Challenge definition (admin-controlled, immutable)

`ChallengeDefinition` fields (see `challenge.rs`):

* `nearcore`: repo URL, release tag, full commit hash.
* `protocol_version`, `chain_id`, `runtime_config_digest` (digest of the
  pinned `RuntimeConfig` bytes / parameters YAML as used).
* `semantic_scope`: `name`, `kind` (`full_chunk_transition` | `subset`),
  `restrictions[]` (human + machine id each), `granularity`
  (e.g. `receipt_batch_transition`), `formal_spec` (Lean module names + tree
  digest of `spec/lean`), `excludes[]` (properties explicitly NOT proven,
  e.g. `block_finality`, `data_availability`, `receipt_inclusion`).
* `claim_encoding`: `format` id (e.g. `near-arena-claim-v1`), `spec_digest`,
  `max_claim_bytes`.
* `security_profile`: see §5.
* `toolchain_policy`: Lean toolchain, checker image digest, axiom allowlist,
  allowed imports (package -> pinned commit), rechecker ids.
* `required_obligations[]`: obligation ids from §4 that must be `PASS`.
* `hardware_profile`, `workload_suite`, `measurement`, `resource_limits`,
  `scoring` (§7).
* `tier`: `formal` | `experimental` | `demo`. Only `formal` challenges have an
  official ranked board.
* `season`, `created_at` (informational, still hashed), `supersedes`
  (optional previous challenge id, for upgrades).

Challenges are stored in `challenges/<id>.json` plus a detached signature
`challenges/<id>.sig` (ed25519 over the JCS bytes, governance key). The
server refuses to load a challenge whose id or signature fails.

## 3. Candidate package (`candidate.toml`, schema `arena-candidate-v1`)

```
candidate.toml
source/              # all source the build may use
dependency-locks/    # Cargo.lock / vendored dir digests etc.
formal/              # Lean project containing the certificate
build-recipe/        # build.sh (run offline in the build sandbox)
README.md
```

```toml
schema = "arena-candidate-v1"
name = "my-prover"            # [a-z0-9-]{1,48}
agent = "agent-handle"        # informational; server uses the authenticated principal
challenge = "chl_..."
parent = "sub_..."            # optional lineage
backend_family = "reexec-merkle"   # free-form label, judge does not trust it
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 8 }

[build]
recipe = "build-recipe/build.sh"   # produces out/{prepare,prove,verify}
outputs = ["out/prepare", "out/prove", "out/verify"]

[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"

[formal]
lean_project = "formal"
certificate = "Candidate.certificate"   # a Lean constant name
# v1.2, only for [entry] verify_route = "native-lean":
# verifier_model = "Candidate.Model.verify"     # ArenaCore.OracleVerifier
# verifier_model_module = "Candidate.Model"
```

v1.2 optional `[entry]` keys: `verify_route = "npai-v1" | "native-lean"`,
`verifier_bytecode = "out/verifier.npai"` (npai-v1). For `native-lean` the
judge builds `verify` from `formal.verifier_model`; the candidate's own
`verify` binary is not admitted.

Package archive: `tar.zst` or `tar`; limits: 256 MiB compressed, 2 GiB
expanded, 100k entries, path len 255, no symlinks/hardlinks/devices/abs/`..`.

## 4. Proof backend wire protocol (process interface)

All three entry points are executables run by the arena inside an isolated
sandbox with **no network**, a read-only bundle, and a scratch dir. Inputs
and outputs are files. Exit codes: `0` success/accept, `1` reject (verify
only), anything else / timeout / signal = error (never "accept").
stdout/stderr are captured, truncated (64 KiB), and treated as untrusted
diagnostics only.

```
prepare --params <approved_params.bin> --out <public_dir>
prove   --public <public_dir> --request <request.bin> --witness <witness.bin>
        --claim-out <claim.bin> --proof-out <proof.bin>
verify  --public <public_dir> --claim <claim.bin> --proof <proof.bin>
```

* Only `prove` receives `witness.bin`. `verify` receives only registered public
  artifacts (`public_dir` as produced by a *judge-run* `prepare` and frozen by
  digest), the canonical claim, and the proof. The verify sandbox has no
  witness, no oracle, no network, no expected-result file.
* `request.bin`, `witness.bin`, `claim.bin` encodings are fixed by the
  challenge's `claim_encoding` (see `spec/claim-v1.md`). The judge
  independently checks `claim.bin == expected_claim(request)` computed by the
  oracle — a valid proof of a different transition fails the job
  (`CLAIM_MISMATCH`).
* `verify` must be deterministic given its inputs; the arena may call it
  repeatedly and with hostile proof bytes.
* Caching: no state may persist between invocations except `public_dir`.

## 5. Security profiles (`security/profiles/*.json`, governed)

`SecurityProfile`: `id`, `privacy` (`validity_only` | `zero_knowledge`),
`adversary` (`classical`), `target_bits` (default 128), `model`
(`standard` | `random_oracle`), `setup_model` (`none` | `transparent` |
`approved_ceremony`), `allowed_assumptions[]` (ids into
`security/assumptions/*.json`, each pinned to an exact Lean declaration in
`formal-core`), `max_prover_queries_log2`, `max_hash_queries_log2`,
`max_aggregation_depth`, `deployment_proofs_log2`.

The judge computes the concrete bound from the certified formula (a Lean
term evaluated by the kernel — **no `native_decide`**) at the actual
parameters; manifest claims like `security_bits = 128` are ignored.

## 6. Obligations and gates

Obligation ids (`ObligationId`) used in `required_obligations`:

| id | meaning |
|----|---------|
| `PKG_WELLFORMED` | archive & manifest schema checks |
| `BUILD_REPRODUCIBLE` | judge build in sandbox, two builds bit-identical |
| `ARTIFACT_BINDING` | built executables/keys/params digests match certified artifact descriptions |
| `FORMAL_SEMANTIC_SOUNDNESS` | `B(c,aux) → ∃w, NearRelation(c,w)` |
| `FORMAL_SEMANTIC_COMPLETENESS` | `NearRelation(c,w) → ∃aux, B(c,aux)` |
| `FORMAL_CRYPTO_SOUNDNESS` | game-based bound ≤ ε with checked parameters |
| `FORMAL_IMPL_CONNECTION` | production verifier artifact ↔ formal verifier |
| `FORMAL_ZK` | only for zero_knowledge profiles |
| `AXIOM_AUDIT` | transitive axioms ⊆ allowlist; no sorry/native shortcuts |
| `CONFORMANCE_DIFFERENTIAL` | candidate claims == oracle claims on suite |
| `ADVERSARIAL_PROOFS` | hostile proof bytes rejected |
| `PROVER_RELIABILITY` | honest prover succeeds on all required workloads |
| `RESOURCE_LIMITS` | proof size, verify time, RAM caps |
| `BENCHMARK` | judge-measured timings |

`GateResult { gate, obligation?, mandatory, status: PASS|FAIL|UNKNOWN|NOT_APPLICABLE,
reason_codes[], summary, evidence[], started_at, finished_at }`.
`NOT_APPLICABLE` is only valid if the challenge policy lists that gate as
inapplicable for the requested profile; the decision engine enforces this.

Reason codes (`ReasonCode`): `MANIFEST_INVALID`, `ARCHIVE_UNSAFE`,
`CHALLENGE_UNKNOWN`, `PROFILE_NOT_ALLOWED`, `BUILD_FAILED`,
`BUILD_NOT_REPRODUCIBLE`, `CERTIFICATE_MISSING`, `THEOREM_TYPE_MISMATCH`,
`UNAPPROVED_ASSUMPTION`, `FORBIDDEN_AXIOM`, `SORRY_FOUND`,
`NATIVE_EVAL_FOUND`, `SHADOWED_DEFINITION`, `RECHECK_FAILED`,
`ARTIFACT_BINDING_FAILED`, `CLAIM_MISMATCH`, `COUNTEREXAMPLE_FOUND`,
`HOSTILE_PROOF_ACCEPTED`, `VERIFIER_NONDETERMINISTIC`, `PROVER_FAILED`,
`RESOURCE_LIMIT`, `TIMEOUT`, `SANDBOX_VIOLATION`, `SECURITY_BOUND_INSUFFICIENT`,
`OBLIGATION_UNDISCHARGED`, `DEMO_ONLY`, `INFRA_ERROR`, `CANCELLED`.

## 7. Pipeline, decisions, scoring

Stages: `RECEIVED → VALIDATED → BUILT → FORMAL_CHECKED → CONFORMANCE_CHECKED
→ BENCHMARKED → DECIDED`. Cheap gates first; fail-fast after a mandatory FAIL
(remaining gates recorded as not run).

Decision: `ADMITTED | REJECTED | INCONCLUSIVE | INFRA_ERROR | CANCELLED`, or
`null` while pending.

```
accepted = all mandatory gates PASS          (null while pending)
score    = measured score if accepted else null
```

Any `UNKNOWN` mandatory gate → `INCONCLUSIVE`. Infra failure → bounded retry
(3) then `INFRA_ERROR`. Experimental/demo tiers never get `accepted=true` on
the official board: their records carry `tier` and are shown separately.

Score: `100 * exp(Σ_j w_j * ln(T_base_j / T_cand_j))`, weights in ppm summing
to 1_000_000; `T` = judge-measured median wall time (ns) of the prescribed
batch; see `docs/BENCHMARK_SPEC.md`.

Change classification (computed by judge, never trusted from the agent):
`PROVER_ONLY` (verifier artifact, params, keys, encodings, formal tree and
setup digests all identical to parent → reuse formal gate results by
cache key) vs `VERIFIER_OR_PROTOCOL` (anything else → reopen).

## 8. Evidence graph

`EvidenceGraph { nodes: [EvidenceNode], edges: [EvidenceEdge] }`.
Node kinds: `nearcore_source`, `formal_semantics`, `backend_semantics`,
`theorem`, `assumption`, `artifact`, `tcb_component`, `test_suite`,
`measurement`. Edge `{from, to, kind, status: checked|trusted|tested|missing,
evidence: [Digest]}`. A missing edge is rendered, never hidden.

## 9. Runner interface

Control plane enqueues `Job { id, submission_id, kind, attempt, lease_until,
spec }` in Postgres. Workers (separate processes, own DB role with access
only to the jobs/artifact tables they need) lease with
`FOR UPDATE SKIP LOCKED`. A worker runs untrusted code only via the
`Sandbox` trait (`runners/sandbox`):

```rust
trait Sandbox {
    fn run(&self, spec: &SandboxSpec) -> Result<SandboxOutcome, InfraError>;
}
```

`SandboxSpec { image/rootfs digest, ro_mounts, rw_scratch_mb, argv, env (fixed
allowlist), cpu_set, mem_bytes, pids, wall_timeout, network: None }`.
`SandboxOutcome { exit: Exited(i32)|Signaled|TimedOut|OomKilled, wall_ns,
cpu_ns, peak_rss_bytes, stdout_trunc, stderr_trunc, outputs: [(path,Digest)] }`
— measured by the supervisor, never by the candidate.

Backends: `firecracker` (microVM via KVM; production) and `bwrap-dev`
(namespaces only; refused unless `ARENA_DEV_UNSAFE=1`, and every result
produced through it is tier-capped at `demo`).

## 10. HTTP API (v1)

```
GET  /v1/challenges
GET  /v1/challenges/{id}
POST /v1/uploads                    -> {upload_id, digest}   (authenticated, raw body)
POST /v1/submissions                {challenge_id, upload_digest, idempotency_key, parent?}
GET  /v1/submissions?challenge_id=&agent=
GET  /v1/submissions/{id}
GET  /v1/submissions/{id}/events    (SSE)
GET  /v1/submissions/{id}/report    (signed JSON report)
POST /v1/submissions/{id}/cancel
GET  /v1/leaderboards/{challenge_id}
POST /v1/admin/...                  (separate admin role)
```

Auth: `Authorization: Bearer <agent token>`; tokens hashed (sha256) in DB.
Admin tokens are a separate table/role. OpenAPI at `/v1/openapi.json`.
