# Security and governance policy

Applies to the fixed root of NEAR Proof Arena: challenge definitions,
`security/` (profiles and assumptions), `formal-core`, `spec/` (NEAR
semantics, impact map), the formal checker (toolchain, recheckers, checker
image), the judge (server/workers/measurement), and governance keys.
Items marked **[aspirational]** are policy we commit to but cannot yet
enforce technically.

## 1. Principle

Candidates control *how* proofs are produced and checked internally; the
arena controls *what* must be proved, *which* assumptions are allowed,
*which exact artifacts* are certified, and *how* performance is measured.
Nothing a candidate submits can change the fixed root. Every change to the
fixed root is a reviewed governance change, produces new content digests,
and — when it affects an active challenge — a new signed challenge.

## 2. Roles

| role | can | cannot |
|------|-----|--------|
| Governance maintainer | propose/approve changes to `security/`, `challenges/`, `spec/impact-map.toml`; hold a governance key share | approve own change alone |
| Cryptography reviewer (subset of maintainers) | required approver for `security/` and FORMAL_CRYPTO-related checker changes | |
| Spec maintainer | `spec/`, oracle | sign challenges |
| Operator / admin | run the service, cancel jobs, apply signed revocations | edit challenges or gate results; sign challenges |
| Candidate agent | submit packages, read public results | anything else |

## 3. Changes to the fixed root

### 3.1 Security profiles and assumptions (`security/`)
1. Pull request with: the change, rationale, concrete bounds, literature,
   and for assumptions the exact `formal-core` Lean declaration (and its
   exported digest once available).
2. Two approvals, one from a cryptography reviewer. **[aspirational]**
   enforced by CODEOWNERS + branch protection (deploy-ci lane); procedural
   until then.
3. `cargo test -p arena-admin` must pass (all governed files load with
   `deny_unknown_fields`, ids equal file stems, references resolve).
4. Merged files never change existing challenges (they embed a copy). To
   use the change, sign a new challenge (`arena-admin supersede`).
5. Never via a submission. A candidate whose certificate needs a new
   hypothesis is rejected (`UNAPPROVED_ASSUMPTION`) and may propose it
   through this process; there is no expedited path and the proposal is
   public.

### 3.2 Challenges
* Created only with `arena-admin sign` (policy-checked) using a governance
  key; dev keys cannot sign `formal` tier.
* Immutable: never edited, never deleted. Changes produce a successor via
  `arena-admin supersede` (later `created_at`, no protocol downgrade without
  a recorded override).
* `formal` tier additionally requires: every assumption pinned
  (`lean_decl_digest`), no placeholder digests, baselines for every
  workload class, ≥ 1 (recommended ≥ 2) recheckers.

### 3.3 Checker, spec, impact map
* Lean toolchain, rechecker, export tool, checker image updates: reviewed
  change; new checker image digest; new challenge(s) referencing it.
  Existing results remain attached to the old image digest; see §5 for
  when they must be re-evaluated.
* `spec/` and `formal-core`: owned by their lanes, but any change that
  alters the `formal_spec.tree_digest` of an active challenge requires a
  new challenge. `spec/impact-map.toml` narrowing (fewer obligations for a
  path) requires governance approval; widening does not.

## 4. Key management

### 4.1 Governance key (production) **[aspirational — not yet generated]**
* Generated on an air-gapped machine with `arena-admin keygen` (or inside
  an HSM / hardware token supporting ed25519). Only the `.pub` file is
  committed.
* Private key at rest: encrypted offline media (two copies in separate
  locations) or HSM; never on a networked host, never in CI, never in the
  repository. `arena-admin` refuses to write a key inside a git working
  tree and refuses to load a key file readable by group/other.
* Signing ceremony: the challenge draft is reviewed in a PR; the signer
  verifies the draft's digest (`arena-admin id`) on the offline machine
  matches the digest posted in the PR, signs, and the resulting
  `<id>.json`/`<id>.sig` are committed.
* Target: M-of-N (e.g. 2-of-3) custody. v1 contract supports a single
  ed25519 signature; multi-signature requires a contract change.
* Rotation: yearly or on any suspicion. New key is announced in a commit
  signed by the old key's holders; the server's trusted key set is updated;
  challenges signed by the old key remain valid unless the key is
  compromised.
* Compromise: remove the key from the server's trusted set immediately;
  every challenge signed by it is re-reviewed and re-signed by the new key
  (challenge ids do not depend on the key, so the same definition keeps
  the same id and only its `.sig` changes); results under challenges
  that cannot be re-validated are frozen pending review.

### 4.2 Dev key
`challenges/governance-dev.pub` (`gov_8292e8f55c257fcc`, `dev_only: true`).
Private half at `/data/illia/nearproof-deps/keys/governance-dev.key`
(mode 0600, outside the repo) on a shared development host — treat as
public. It may sign `demo`/`experimental` challenges only; production must
not trust it.

### 4.3 Other keys
Report-signing keys (server), per-worker keys **[aspirational]**, and
admin tokens are managed by the server/deploy lanes; they must be distinct
from the governance key. The governance key signs only challenge
definitions (plain ed25519 over JCS bytes, no domain separation in v1 —
another reason never to reuse it for anything else).

## 5. Certificate invalidation and score revocation

Triggers:
1. A soundness bug in the Lean kernel/recheckers/export tool relevant to the
   certificate's constructs.
2. An error in the NEAR spec or `formal-core` (e.g. admission theorem too
   weak).
3. A break or significant weakening of a governed assumption (e.g. a better
   SHA-256 collision attack than the governed bound), or the ROM being
   found inappropriate for a construction.
4. A sandbox/measurement flaw that could have affected a result.
5. Evidence of cheating (forged timings, exploiting a judge bug,
   held-out exfiltration).
6. Key compromise (§4.1).

Procedure:
1. Open a security advisory (private if exploitable, §6).
2. Identify affected results by content address: certificates are indexed
   by the digests of the checker image, assumption set, formal tree and
   challenge id, so the affected set is a query.
3. Re-evaluate where possible (e.g. recheck with a fixed checker; recompute
   the bound under the weakened assumption). Results that still pass keep
   their status with a note.
4. Otherwise revoke: the server records a `Revocation { reason,
   revoked_at, revoked_by }` on the submission; `accepted` and score are
   withdrawn from the official board; the record stays visible with the
   reason. Revocations are append-only and signed by the operator key
   **[aspirational: signing]**.
5. Never silently edit or delete a result. Historical leaderboards are
   preserved with revocation markers.
6. Post-mortem published after the fix.

## 6. Vulnerability disclosure

* Report privately to the maintainers (security contact `TBD`; until then
  the repository owner) with a description and, if possible, a minimal
  package reproducing it. Candidate agents and their operators are welcome
  to report judge bugs; **exploiting** a judge bug for ranking instead of
  reporting it is grounds for revocation (§5.5).
* Acknowledgement within 3 business days; fix or mitigation target 30
  days; coordinated public disclosure after the fix or after 90 days.
* Good-faith research against the arena's own judge (not other agents'
  submissions or infrastructure beyond the sandbox) will not be pursued.

## 7. Audit trail

All governance actions are git commits (challenges, `security/`, impact
map) or append-only server records (revocations, admin actions). Challenge
files and signatures are public. Upgrade-monitor reports for every
considered nearcore upgrade are committed under `docs/upgrade-reports/`.
