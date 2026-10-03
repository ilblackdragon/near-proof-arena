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
   refer to classes (and cover all classes for `formal`).
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
$A verify --pubkey challenges/governance-prod.pub --all-in challenges
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
* The production governance key does not exist yet. It must be generated on
  an offline machine (or inside an HSM) per `docs/SECURITY_POLICY.md`; only
  its `.pub` file is ever committed.

## Current contents

| id | tier | name | notes |
|----|------|------|-------|
| `chl_54c65fe7c73c5abcfe500681889177bc` | demo | `demo-toy-arithmetic` | Plumbing fixture: `c = a·b mod 2^64`. **Not NEAR semantics.** Signed with the dev key. |

`templates/near-transfer-receipt-v1.template.json` is the skeleton for the
first formal challenge. Every `TODO(spec-lane)` field (relation, spec and
claim-encoding digests, runtime config digest, workloads) must come from the
spec-oracle lane; this lane does not define the NEAR slice.
