# Protocol upgrades

How the arena follows nearcore releases and NEAR protocol upgrades without
ever letting a result silently change meaning.

## 1. Invariants

1. A challenge pins **one** nearcore commit (`nearcore.commit`, full hash),
   one `protocol_version`, one `chain_id` and one `runtime_config_digest`.
   It never changes.
2. Every semantic change (anything that can alter `NearRelation`, the claim
   encoding, runtime parameters, or the oracle's outputs on the challenge
   scope) gets a **new challenge** that `supersedes` the old one.
3. Results are bound to the challenge id they were measured under.
   Historical rankings are preserved and displayed with that challenge;
   superseding never re-labels, re-scores or deletes them.
4. Unknown versions fail closed: the judge never evaluates a request,
   oracle output or chain context whose protocol version is not the
   challenge's.
5. "The old Lean proof still compiles" is never evidence that it still
   applies.

## 2. Upgrade flow

```
new nearcore release / protocol version
        │
        ▼
1. fetch the new ref into a governance nearcore clone (pinned checkout is untouched)
2. tools/upgrade-monitor --old <challenge pin> --new <ref>         ──► report (JSON+MD)
        │  exit 0 NO_SEMANTIC_CHANGE_DETECTED   exit 3 REVALIDATION_REQUIRED   exit 2 error
        ▼
3. commit the report under docs/upgrade-reports/
4. if exit 0: optional — a new challenge is still required if the operator wants
   results to cite the new commit; otherwise the old challenge stays active.
   if exit 3/2: for each impacted rule (spec/impact-map.toml):
     a. spec lane updates spec/lean + claim encoding + fixtures (new tree digests)
     b. oracle lane rebuilds the oracle at the new commit; runs conformance
        of the *spec* against the new oracle
     c. formal-core / checker changes if any
5. governance drafts the successor ChallengeDefinition (new nearcore pin,
   protocol_version, runtime_config_digest, formal_spec digests, workloads,
   held-out commitment, created_at) and signs it:
     arena-admin supersede --old challenges/<old>.json --draft <new>.json …
   (rejects protocol_version downgrade and non-increasing created_at)
6. announce; old challenge enters "superseded" state: still verifiable,
   still listed with its rankings, closed for new submissions after a
   published grace period (server lane). **[not implemented]** the server
   ignores `supersedes` today. An admin closes the old challenge manually
   with `POST /v1/admin/challenges/{id}/status` (`open = false`).
7. candidates re-submit against the new challenge. Formal results are NOT
   carried over automatically — the judge's PROVER_ONLY cache key includes
   the challenge id, so every obligation is re-run.
```

The monitor exits non-zero whenever *anything* in the runtime closure
changed (files, external crate versions, parameters, protocol constants,
`ProtocolFeature` set, closure membership, parse failures). The impact
map only decides *which* obligations/spec definitions to look at first;
the default for an unmapped change is "everything semantic".

Sample: `docs/upgrade-reports/nearcore-2.13.3-to-2.13.4.md` shows that even a
patch release with an unchanged protocol version (86) modifies state
commitment code (`near-primitives` state parts, `near-store` trie), and
therefore requires revalidation.

## 3. Fail-closed handling of unknown versions

* The oracle is built from exactly `nearcore.commit` and refuses requests
  whose embedded protocol version ≠ `challenge.protocol_version`
  **[aspirational: oracle lane to implement the check]**.
* The claim encoding (`near-arena-claim-v1`) must include the protocol
  version and chain id in the claim, so a proof for one version can never
  be presented as a proof for another **[spec lane to confirm]**.
* The server refuses to load a challenge whose id/signature fails
  (implemented, and re-verified on every read). It refuses submissions to
  closed challenges (`open = false`); automatic closing of superseded
  challenges after the grace period is **[not implemented]**.
* The upgrade monitor treats unparseable protocol facts, missing root
  crates, and git/cargo failures as REVALIDATION_REQUIRED (exit 2/3).

## 4. Authenticating the version against chain context

An admitted prover proves `NearRelation_v(c, w)` for the challenge's
version `v`. A *consumer* of such proofs (e.g. a light client) must know
that the chunk it is checking was produced under `v`:

* The claim binds `protocol_version` and `chain_id`; the consumer compares
  them with the epoch's protocol version from the block header / epoch info
  it already trusts. **[aspirational]** the arena does not verify finality,
  epoch transitions or header chains — `block_finality`,
  `receipt_inclusion` and `data_availability` are in every challenge's
  `excludes`.
* Upgrade boundaries: the first block of an epoch with a new protocol
  version must be proven under the successor challenge. Proofs straddling
  an upgrade boundary are out of scope for v1.
* The runtime config actually used on-chain at version `v` must equal the
  challenge's `runtime_config_digest`; the spec lane computes this from the
  pinned parameters YAML for the challenge's `chain_id` (mainnet and
  testnet differ: `parameters.yaml` vs `parameters_testnet.yaml`).

## 5. Historical rankings

* Leaderboards are per challenge id. A superseded challenge's board is
  frozen, not deleted, and shows a "superseded by chl_…" banner
  (**[not implemented]**: neither the server nor the web links successors yet).
* Cross-version comparisons are not computed: different relations,
  parameters and workloads make scores incomparable.
* Revocations (SECURITY_POLICY §5) can still be applied to historical
  results, e.g. if a spec bug is found that also affected the old version.

## 6. Limitations

* The monitor's closure is a static over-approximation of crate
  dependencies; it does not trace `build.rs` file reads or non-literal
  `include!`s (see `tools/upgrade-monitor/README.md`).
* The initial impact map uses `concept:` placeholders until the spec lane
  names exact Lean declarations and fixture paths.
* No newer nearcore release than 2.13.4 exists at the time of writing; the
  committed reports therefore compare older tags *to* 2.13.4.
