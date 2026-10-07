# D3α read-set reference

`reexec-v3-d3` is the witness re-execution reference for the unified
`near-chunk-v3` challenge, declared tier `D3a`. It is **not a succinct proof**:
the proof contains the recorded-store bytes needed to execute the transition.
The verifier establishes the original frozen `NearSpecV3.D3.RelD3` relation.

The prover executes the proved logged checker once, then serializes the exact
recorded-store answers read by that execution. The verifier also executes the
logged checker once and accepts only if re-encoding its read set gives exactly
the supplied proof bytes. There is no fallback accepting noncanonical bytes.

## Encoding

* Ignored chunk height/signature and transition block hashes are zeroed.
* Receipt-proof entries retain the producer's bytes, with one last-wins entry
  per key in increasing byte order.
* The main `base_state ++ contract_code` store is tag zero; implicit transition
  `k` has its own store at tag `k + 1`.
* Each store keeps exactly the successful answers to its logged read keys,
  with one last-wins value per hash, in byte order. Missing answers remain
  missing. Hash collisions require no injectivity assumption for these proofs.
* The existing deterministic `encP` layout divides the main pool into trie
  values and code blobs; its large-state-witness fallback keeps the state
  witness within 8 MiB. Everything outside the normalized fields is preserved.

`source/prover/ProveMain.lean` emits `Read.canonW`. `Model.lean` decodes the claim
and calls `Read.check`; the native verifier is this Lean definition compiled by
the governed compiler. The implementation connection remains the challenge's
`native-lean` trusted compiler edge. `build-recipe/build.sh` lists the exact
35-module candidate model closure and uses the frozen vendor unchanged.

## Proofs

| Property | Module / theorem |
|---|---|
| Logged execution equals the frozen D3 checker | `Logged.API.checkD3Reads_eq` |
| Acceptance implies the frozen relation and literal normality | `ReadCanon.check_sound`, `check_normal` |
| Filtering pools is exact tagged-store restriction | `ReadPools.poolStore_restrict` |
| Serialized bytes implement that restricted store | `ReadStores.storesOf_encodeReads` |
| Re-encoding preserves checker control flow and successful reads | `ReadReencode.checkD2CoreL_reencode`, `canonW_refines` |
| Every valid witness yields accepted bytes of no greater length | `ReadComplete.check_canonW` |
| Normalization is a literal byte fixed point | `ReadComplete.canonW_idempotent` |
| Full native-route admission and unified-statement soundness | `Obligations.admission`, `statementSound` |

The distinct-program simulation is separate from the fixed-program store
restriction theorem: `reads_restrict_eq` alone does not establish re-encoding
congruence. `ReadComplete` composes both proved halves. The older necessity
normalizer remains as supporting encoding/proof infrastructure; it is no longer
the deployed normalization path.

## Candidate-local logged library

`formal/ReexecV3D3/Logged/` contains 30 candidate-local copies from upstream
commit `77b844e0e81d9536e8885b4c35ff9f0b89a7af88`. The only transform is literal
replacement of `NearSpecV3.Logged` with `ReexecV3D3.Logged` in imports, namespaces
and references. `dependency-locks/logged-candidate.json` records both hashes
for every file. Reproduce with `source/verifier/sync-logged.py COMMIT`, or add
`--check` for read-only verification.

These are candidate proof/code modules, outside the judge's trusted module set.
The frozen `source/lean-vendor` and the signed challenge's trusted set are
unchanged. Twenty-five guarded transitive axiom checks pass in
`test/AuditReadLocal.lean`; the new completeness proofs use only the permitted
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Validation status

The read-set proof stack and wired Model/prover/local certificate have compiled,
including complete normalization and non-expansion. Fresh native builds, actual
formal audit and hostile `check-local` runs are in progress. No candidate admission or hostile-suite pass
is claimed for this revision yet. Required hostile mutations include
`values/inject-unread` and `codes/inject-unread` on both public and held-out sets.

Historical reference results in `docs/e2e-results/v3-d3-reference/` concern the
previous necessity normalizer. Fresh logged checker validation is documented in
`docs/e2e-results/v3-wasm-logged/` and the D1/D2 logged-checker reports; TTN replay
is being regenerated separately against the pinned nearcore harness.

The relation remains a tested transcription of nearcore, not a proof of equality
to its Rust implementation. D3 is the cold-cache statement: a warm-cache
nearcore validator can accept witnesses without code blobs that `RelD3` rejects.
