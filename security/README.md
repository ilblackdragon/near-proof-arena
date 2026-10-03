# `security/` — governed security profiles and assumptions

Everything in this directory is part of the arena's **fixed root**. Candidates
never add to it, modify it, or influence it through a submission. A candidate
can only *request* one of the profiles listed here
(`security_profile_request` in `candidate.toml`), and only if the challenge it
targets embeds that exact profile.

```
security/
  profiles/<id>.json      SecurityProfile  (arena-types::security::SecurityProfile)
  assumptions/<id>.json   Assumption       (arena-types::security::Assumption)
```

Both types are parsed with `deny_unknown_fields`; `id` must equal the file
stem; every `allowed_assumptions` entry of a profile must name a file in
`assumptions/`. `cargo test -p arena-admin` and
`arena-admin check-governed` enforce this.

## Profiles

| id | privacy | model | setup | target | hash-query budget | proof attempts |
|----|---------|-------|-------|--------|-------------------|----------------|
| `validity-classical-128` | validity only | ROM (Fiat–Shamir) | transparent | 128 bits | 2^64 | 2^40 |
| `zk-classical-128` | zero knowledge | ROM (Fiat–Shamir) | transparent | 128 bits | 2^64 | 2^40 |

Both are **classical** profiles: nothing here implies post-quantum security.
Both forbid trusted setups (`setup_model = transparent`); an
`approved_ceremony` profile would need its own governance change including the
ceremony transcript digest and an analysis of trapdoor residue.

Parameter rationale (reviewed values, not derived by the tooling):

* `max_hash_queries_log2 = 64` — the adversary may evaluate the random oracle
  2^64 times in total. The certified bound must be an explicit function of
  this budget, evaluated at 2^64 by the Lean kernel (no `native_decide`), and
  must be ≤ 2^-128 *after* accounting for it. Note that a bound of the shape
  `q_H · ε` therefore needs per-query error ≤ 2^-192.
* `max_prover_queries_log2 = 40` — number of proof attempts / verifier
  queries an adversary can make against a deployed verifier.
* `deployment_proofs_log2 = 40` — number of honest proofs assumed to be
  produced over the lifetime of a deployment (relevant to ZK/simulation and to
  multi-instance union bounds).
* `max_aggregation_depth = 8` — maximum recursion/aggregation depth for which
  the bound must hold (losses compound per level).

The judge never trusts a manifest's claimed security level; it evaluates the
certified bound at the challenge's concrete parameters (CONTRACTS §5).

## Assumptions

| id | kind | Lean hypothesis (formal-core) |
|----|------|-------------------------------|
| `sha256-collision-resistance` | falsifiable, concrete-security, explicit reduction | `Arena.Assumptions.Sha256CollisionResistant` |
| `random-oracle-fiat-shamir-sha256` | idealised **model** with query budget | `Arena.Assumptions.RandomOracleFiatShamirSha256` |

An assumption file is a *pointer* to an exact Lean declaration in
`formal-core`. Cryptographic assumptions enter certificates **only as
explicit hypotheses** of the certified theorem, never as Lean `axiom`s (the
axiom allowlist of a challenge may contain only `propext`,
`Classical.choice`, `Quot.sound`; `arena-admin` rejects anything else).

`lean_decl_digest` is currently `null` in both files: the `formal-core` lane
has not yet published the declarations. **Until it is filled, no `formal`
tier challenge can be signed** — `arena-admin` refuses formal challenges that
allow an unpinned assumption. This is intentional fail-closed behaviour.

## Governance: how this directory changes

Adding, removing or editing any file here is a **governance change**, never a
side effect of a submission:

1. A pull request touching `security/` must be reviewed and approved by at
   least two governance maintainers, one of whom is a cryptographer, and
   must include: the exact Lean declaration (and its digest once
   `formal-core` exports it), the concrete bound and its justification, and
   literature references.
2. CODEOWNERS / branch protection for `security/` is the deploy-ci lane's
   job (see `docs/SECURITY_POLICY.md`); until it exists this rule is
   procedural only.
3. Existing challenges embed a **copy** of their profile and are signed; an
   edit here never changes the meaning of a published challenge. To apply a
   change to an active challenge, governance signs a new challenge that
   `supersedes` the old one (`arena-admin supersede`).
4. Weakening (removing an assumption from use, discovering an attack, lowering
   a budget) follows the invalidation procedure in
   `docs/SECURITY_POLICY.md`: affected certificates are re-evaluated and
   scores revoked where the bound no longer holds.
5. Assumptions are never added because a candidate needs them. A candidate
   whose certificate depends on an unlisted hypothesis gets
   `UNAPPROVED_ASSUMPTION`; it may *propose* an assumption out of band, and
   the proposal goes through steps 1–3 with no expedited path.
