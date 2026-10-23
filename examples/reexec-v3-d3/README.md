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
26-module candidate model closure and uses the frozen vendor unchanged.

## Proofs

| Property | Module / theorem |
|---|---|
| Logged execution equals the frozen D3 checker | `Logged.API.checkD3Reads_eq` |
| Acceptance implies the frozen relation and literal normality | `ReadCanon.check_sound`, `check_normal` |
| Acceptance decomposes into the relation **and** canonicality (strictly stronger than `RelD3`) | `ReadCanonSplit.check_iff`, `relD3_of_check` |
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

`formal/ReexecV3D3/Logged/` derives from 30 upstream modules at commit
`77b844e0e81d9536e8885b4c35ff9f0b89a7af88`. The reproducible transform replaces
`NearSpecV3.Logged` with `ReexecV3D3.Logged`, then moves unchanged computational
declarations into `Logged/Runtime/` and rewires imports. Runtime declaration bodies are preserved. This keeps proof metaprogramming out of the
model's native import closure. `dependency-locks/logged-candidate.json` records
upstream hashes, exact extracted source ranges and their hashes, import edits,
recorded proof-only patches, and every resulting file hash. Reproduce with `source/verifier/sync-logged.py
COMMIT`, or add `--check` for read-only verification.

These are candidate proof/code modules, outside the judge's trusted module set.
The frozen `source/lean-vendor` and the signed challenge's trusted set are
unchanged. Twenty-five guarded transitive axiom checks pass in
`test/AuditReadLocal.lean`; the new completeness proofs use only the permitted
Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Validation status

The read-set proof stack and wired Model/prover/local certificate have compiled,
including complete normalization and non-expansion. The runtime split passed two reproducible native builds and public SDK gates.
Actual worker validation passed 407 public and 208 held-out positive cases,
244 public and 64 held-out negatives, and all 4,495 hostile mutations, including
`values/inject-unread` and `codes/inject-unread` on both sets. The held-out SDK also passed its two reproducible builds and all six applicable
local gates.

Configured formal checking now passes every gate (2026-10-13, lane `d3-lean4lean`): artifact
binding, leanchecker (72 modules), nanoda and lean4lean (72 modules), with default checker limits and
the unchanged three-checker policy. lean4lean had rejected `W.E_exec` for deep recursion: its
`memFill`/`memCopy` cases (and the generated `exec.eq_36`/`exec.eq_37`) made the kernel reduce
`memBytes s = s.pages.size * 65536` with a symbolic factor, which lean4lean's `Nat` literal
extension unfolds 65,536 levels deep. The fix is proof-only: `E_exec` unfolds `exec` by
`exec.eq_def` and abstracts `memFill`/`memCopy` before reducing (`opaque_gen`). It is recorded as a
proof patch (`source/verifier/logged-proof-patches/WasmStepE.json`) applied by `sync-logged.py`.
Statements, runtime declarations and all three native binaries are unchanged (byte-identical
`prepare`/`prove`/`verify`), so the native and worker gate results below still apply. Evidence:
`docs/e2e-results/v3-d3-read-reference/report.json` (`configured_formal_lean4lean`) and
`docs/logs/d3-lean4lean-2026-10.md`.

Re-check at the near-chunk-v3 re-freeze (2026-10-14, lane `v3-d3-recheck`): the draft was
re-frozen at `3c2a4563` (trusted tree `b890e835…`, adds `Tier.d0a`; draft id
`chl_3e63bc79…`). The vendor was re-synced (`sync-vendor.sh 3c2a4563`: `ChallengeChunkV3` changed,
`NearSpec.TrieUpsertProofs`, `NearSpecV3.ChunkValidationV0a`, `PrepD0`, `ChallengeD0a` added) and
`build.sh` links the config's full trusted module list, as the judge does. No candidate Lean source
changed. The configured formal check passes every gate again (leanchecker 72/72, nanoda,
lean4lean 72/72; default limits). `prepare` is unchanged (`8341e9de…`); `prove` (`14dd38be…`) and
`verify` (`bdbc3eef…`, equal to the judge's build) changed only because more trusted modules
are linked. With the new binaries: SDK check-local passes (package `73782d64…`), the strict public
gate passes (407/407 positives, byte-identical proofs, 244/244 rejections) and so do all
3,062 worker mutations; held-out 208/208 positives (identical proofs) and 1,433 mutations pass. Evidence: `docs/logs/v3-d3-recheck-2026-10.md`.

Re-check at the near-chunk-v3 re-freeze with tier D1a (2026-10-14, lane `v3-refreeze-v3`): the
draft was re-frozen at `85adc6c0` (trusted tree `66bba27e…`, adds `Tier.d1a`; ranks D0a 0, D0 1,
D1a 2, D1 3, D2 4, D3a 5; draft id `chl_497bbbf1…`). The vendor was re-synced (`sync-vendor.sh
85adc6c0`: `ChallengeChunkV3` changed, `NearSpecV3.ChunkValidationD1a` added) and `build.sh` links
the config's 64 trusted modules. No candidate Lean source changed. The configured formal check
passes every gate (leanchecker 72/72, nanoda, lean4lean 72/72; default limits). `prepare` is
unchanged (`8341e9de…`); `prove` (`8859b7d2…`) and `verify` (`cda17614…`, equal to the judge's
build) changed only because one more trusted module is linked. The strict public gate passes
(407/407 positives with byte-identical proofs, 244/244 rejections). Evidence:
`docs/logs/v3-refreeze-v3-2026-10.md`.

Historical reference results in `docs/e2e-results/v3-d3-reference/` concern the
previous necessity normalizer. Fresh logged checker validation is documented in
`docs/e2e-results/v3-wasm-logged/` and the D1/D2 logged-checker reports; TTN replay
is being regenerated separately against the pinned nearcore harness.

The relation remains a tested transcription of nearcore, not a proof of equality
to its Rust implementation. D3 is the cold-cache statement: a warm-cache
nearcore validator can accept witnesses without code blobs that `RelD3` rejects.
