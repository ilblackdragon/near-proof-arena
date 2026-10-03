# `challenges/` — signed, immutable challenge definitions

```
challenges/
  chl_<32 hex>.json        ChallengeDefinition (pretty JSON, every field explicit)
  chl_<32 hex>.sig         ed25519 signature (128 lowercase hex + "\n") over JCS(definition)
  governance-dev.pub       DEV-ONLY governance public key (see below)
  drafts/                  unsigned inputs used to produce the signed files
  templates/               fill-in templates; NOT challenges, never loaded by the server
  demo/<name>/             supporting material (spec doc, Lean relation, generators, fixtures) for demo challenges
```

## Rules enforced by `arena-admin verify` (and to be enforced by the server)

1. The file parses as `arena_types::ChallengeDefinition` (`deny_unknown_fields`)
   and is in normal form: re-serializing the typed value yields the same JCS
   bytes (no omitted `null` options).
2. `chl_` + first 32 hex of `sha256(JCS(def))` equals the file stem.
3. `<id>.sig` verifies (`ed25519` `verify_strict`) under a trusted governance key.
   A key with `dev_only: true` may not sign `tier: formal`.
4. `security_profile` is byte-for-byte equal to `security/profiles/<id>.json`;
   all its assumptions exist; for `formal` tier every assumption is pinned
   (`lean_decl_digest` non-null).
5. Workload weights sum to exactly 1 000 000 ppm, class ids unique, baselines
   refer to classes; for `formal` they cover all classes, or are entirely
   absent (`baseline_submission = null`, `baseline_ns = []`: admissions are
   decided, scores stay null until a superseding challenge pins baselines).
   `formal` also requires `formal_params` with
   `max_proof_bytes == resource_limits.max_proof_bytes`.
6. Obligations are consistent with tier and privacy:
   * `formal`: every obligation is required, except `FORMAL_ZK` under a
     `validity_only` profile;
   * `validity_only` (any tier): `FORMAL_ZK` is in `not_applicable_gates` and not required;
   * `zero_knowledge`: `FORMAL_ZK` is never not-applicable;
   * only `FORMAL_ZK` may ever be not-applicable; nothing is both required and N/A;
   * `experimental` requires at least PKG/BUILD/BINDING/CONFORMANCE/ADVERSARIAL/RELIABILITY/RESOURCE;
     `demo` requires at least `PKG_WELLFORMED`.
7. Axiom allowlist ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; formal tier
   names ≥ 1 rechecker; `formal_spec.lean_toolchain == toolchain_policy.lean_toolchain`.
8. The all-zero digest `sha256:000…0` is the only allowed placeholder and only
   in `demo` tier.

The server lane can link `arena-admin` as a library
(`arena_admin::verify_file`) to apply identical rules.

## Workflow

```sh
cargo build -p arena-admin
A=target/debug/arena-admin
$A check  challenges/drafts/<draft>.json            # policy only
$A id     challenges/drafts/<draft>.json            # chl_… and full digest
$A sign   challenges/drafts/<draft>.json --key /offline/governance.key
$A verify --pubkey challenges/governance-local.pub --pubkey challenges/governance-dev.pub --all-in challenges
$A supersede --old challenges/chl_old.json --draft new.json --key … --pubkey …
$A tree-digest challenges/demo/toy-arithmetic/lean  # TreeDigest helper
```

Challenges are never edited or deleted. A change of anything (nearcore
release, parameters, spec, workloads, profile) produces a **new** challenge
whose `supersedes` names the old one; the old file stays so historical
rankings remain attached to the definition they were measured against
(`docs/PROTOCOL_UPGRADES.md`).

## Keys

* `governance-dev.pub` (`key_id gov_8292e8f55c257fcc`) is a **DEV-ONLY** key.
  Its private half is on a shared development host
  (`/data/illia/nearproof-deps/keys/governance-dev.key`, outside the repo,
  mode 0600) and must be considered compromised for any production purpose.
  It can sign `demo`/`experimental` challenges only; a production deployment
  must not list it as a trusted key.
* `governance-local.pub` (`key_id gov_7e075bd83a3313b5`) is the **local
  deployment operator key — not a NEAR Foundation / production governance
  key**. Private half: `/data/illia/nearproof-deps/keys/governance-local.key`
  (0600, outside the repo). It is not dev-only, so it can sign `formal` tier
  for this local deployment; a public deployment must replace it with a real
  governance key (and re-sign via `supersede`).
* The production governance key does not exist yet. It must be generated on
  an offline machine (or inside an HSM) per `docs/SECURITY_POLICY.md`; only
  its `.pub` file is ever committed.

## Current contents

| id | tier | name | notes |
|----|------|------|-------|
| `chl_54c65fe7c73c5abcfe500681889177bc` | demo | `demo-toy-arithmetic` | Plumbing fixture: `c = a·b mod 2^64`. **Not NEAR semantics.** Signed with the dev key. |
| `chl_5ef2bc7d2068219635426e47ca46bfbb` | formal | `near-transfer-receipt-v1` | `near/pv86/receipt-transfer-batch/v0` (nearcore 2.13.4, PV 86): Transfer-receipt batches, relation `NearSpec.TransferV1.NearRelation`. Signed with the local operator key. Baselines not yet measured. Draft built by `spec/tools/build_challenge_draft.py`. |

| `chl_f7eb2d91bf7b363eee134b6ad9d3e011` | formal | `near-transfer-receipt-v1-1` ("v1.1") | **Supersedes `chl_5ef2…`.** Identical semantics, spec, claim encoding, workloads, procedure and limits; only pins the baseline: `baseline_submission = sha256:329c763a…bcd699f` (package digest of `examples/reexec-witness`, git tree `6dfbc3bc…`) and `baseline_ns` = batch-1 213 592 463, batch-16 205 044 335, batch-256 216 310 937. Why: under v1 `baseline_ns = []`, so every score was null. The baselines are **dev-host** medians (`benchmarks/results/baseline-near-transfer-receipt-v1-r1-devhost-20261003/`), not governed-hardware numbers. Draft: `drafts/near-transfer-receipt-v1-1.draft.json` (`benchmarks/baseline/pin_baseline.py`). Signed with the local operator key. |
| `chl_3be93793610370275ae40f36a475f01f` | formal | `near-transfer-receipt-v1-2` ("v1.2") | **Supersedes `chl_f7eb…`; current head of the NEAR chain.** Same semantics, spec, claim encoding, workloads and limits as v1.1. Three changes: (1) `toolchain_policy.checker_image` = `sha256:b6391b3899df90e2557924ae7b67f0c07456fa20d41f6bbf383220a311d15b1e`, the checker identity that the Firecracker FORMAL_CHECK worker reports for the production lean-checker image `sha256:d85133a1…` (v1/v1.1 pinned the identity of one host build of the checker tools, so their formal gates were UNKNOWN in production); (2) `measurement.invocation_mode = vm_per_batch` (bench-spec-v1.1); (3) a baseline re-measured under that procedure through Firecracker: `baseline_submission = sha256:329c763a…bcd699f` (same reference package), `baseline_ns` = batch-1 6 828 348, batch-16 7 226 875, batch-256 10 195 296 (**dev-host**, calibration passed; `benchmarks/results/baseline-near-transfer-receipt-v1-2-vmperbatch-devhost-20261003/`). The measurement ran against the unsigned pre-baseline draft `drafts/near-transfer-receipt-v1-2.measure.json` (`chl_30f39d9b…`, which is also where the sampling seeds come from); `drafts/near-transfer-receipt-v1-2.draft.json` is that draft plus the baseline (`pin_baseline.py --base`). Signed with the local operator key. |

Names are `[a-z0-9-]` only, so "v1.1" is spelled `v1-1` (and "v1.2" `v1-2`). `created_at` is a
governance-declared timestamp (v1: `2026-10-03T12:00:00Z`, v1.1:
`2026-10-03T13:00:00Z`); `supersede` only requires it to increase. The
reference package still names `chl_5ef2…` in its `candidate.toml`: the pinned
`baseline_submission` is that exact package, measured on v1 inputs, which are
semantically identical to v1.1's.

`templates/near-transfer-receipt-v1.template.json` is the skeleton the draft
builder fills from `spec/challenge-inputs/` (spec-oracle lane).
