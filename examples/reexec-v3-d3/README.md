# reexec-v3-d3: reference candidate for `near-chunk-v3`, declared tier D3a

The re-execution reference of **`near-chunk-v3`** ("NEAR chunk state-transition succinct proof"), the
coverage-tiered challenge of docs/CONTRACTS.md §11 (statement `near/pv86/chunk-validation/v0`,
relation `NearSpecV3.RelChunkV3 = RelD0 ∨ RelD1 ∨ RelD2 ∨ D3.RelD3`,
`spec/lean/v3/NearSpecV3/ChallengeChunkV3.lean`). It declares the largest tier, **`D3a`**
(`candidate.toml [entry] declared_tier`), and is admitted under
`NearSpecV3.challengeParamsChunkWith .d3a …`: soundness w.r.t. `D3.RelD3` (lifted to the statement by
the trusted `NearSpecV3.sound_lift`) and completeness on `DomainTier .d3a`. Backend family
**re-execution witness**: the proof is the witness file (the real nearcore `ChunkStateWitness` and the
contract code blobs) in **normal form**, and the verifier decides `NearSpecV3.D3.checkD3` on it. It
never answers `UNSUPPORTED`.

## Layout

| path | what |
|---|---|
| `source/src/bin/prepare.rs` | Rust, std only: checks `near-arena-params-v3` (domain `D3a`) and copies it to `public.bin` |
| `source/prover/ProveMain.lean` | `prove` (Lean, linked with the same compiled trusted + model objects as `verify`): `claim.bin = request.bin`, `proof.bin = ReexecV3D3.proveW` of the witness |
| `source/src/bin/leanorder.rs` | build helper: the judge's trusted-module link order |
| `source/lean-vendor/` | verbatim copies of the judge-trusted Lean modules of `near-chunk-v3` (`runners/formal-checker/challenges/near-chunk-v3.json`: `ArenaCore`, 11 `NearSpec`, 47 `NearSpecV3` modules) at the freeze commit `8926b431`; `source/verifier/sync-vendor.sh 8926b431`; digests in `dependency-locks/lean-vendor.sha256` |
| `formal/ReexecV3D3/` | `Canon` (normaliser, `normalW`, `proveW`), `Model` (verifier), `Obligations`, `PublicBin`, `Certificate` |
| `judge-local/` | local emulation of the judge-generated `ArenaExpected` (template `spec/lean/judge/ExpectedChunkV3.native-lean.lean.template`, `declared_tier` = `NearSpecV3.Tier.d3a`) |
| `build-recipe/build.sh` | offline reproducible build of `out/{prepare,prove,verify}`, step for step the judge's native-lean build |

## Verifier

```lean
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => normalW c.encode pb && acceptsD3 c.encode pb      -- acceptsD3 ↔ D3.RelD3
```

## Normal form (`formal/ReexecV3D3/Canon.lean`)

`canonW cb w` fixes every degree of freedom that nearcore's validator (and `RelD3`, which mirrors it)
leaves in a witness file:

| freedom | normal form |
|---|---|
| chunk header `height_included`, chunk signature, every transition `block_hash` (never read) | 0 / ED25519 + 64 zero bytes / 32 zero bytes |
| `source_receipt_proofs` (`HashMap`: any order, a duplicate key keeps the last value) | one entry per key (the last), increasing key order; entry bytes are the producer's |
| main `base_state` (hash-indexed store: any order, duplicates, unread values) | the values **reachable** from the chunk's `prev_state_root` through the merged store `base_state ++ code blobs` (trie nodes by child hash, leaf values by value hash), deduplicated, increasing SHA-256 order |
| implicit transition *i*'s `base_state` | the same from its pre-state root (the previous transition's `post_state_root`) through its own values |
| contract code blobs (appended to the main store: any order, duplicates, unused blobs, blobs that are also trie values) | the blobs of the merged store that are not reachable (above) and are **needed**: removing one from the code list makes `checkD3` fail (cold-cache rule: an executed pre-state contract's code must be in the witness), deduplicated, increasing SHA-256 order — one `checkD3` run per candidate blob |

Everything else (header inner, receipts and merkle paths, applied-receipts hash, both transaction
lists, post-state roots) is the producer's bytes.

**Residual freedom (stated, not closed): reachable but unread values.** A `base_state` value is kept
iff its SHA-256 is referenced, as a child or as a leaf value, by a node that is itself kept, starting
at the pre-state root. An honest witness holds exactly nearcore's read set, which is closed under that
rule (every recorded node was read along a path from the root), so the normal form of an honest
witness is its read set. But a value that is the true preimage of a hash referenced by a kept node,
and that the relation never reads (e.g. a sibling subtree's node, or a `ContractCode` value of an
account whose leaf is read but whose contract is not called), is accepted in `base_state` too:
nearcore accepts it and so does `RelD3` (the D2 relation reveals the whole recorded store), and the
normal form keeps it. Exploiting it needs the real bytes of state the chunk did not touch; the
judge's freedom mutators (reorder, duplicate, unreferenced junk) cannot produce it. Closing it would
need the exact read set of the D2/WASM runtime (an instrumented re-execution), as the D0 reference
does for its much smaller runtime; the D1/D2 normaliser handoff (`examples/reexec-v3-d2`) has the
same residual freedom.

## The escape clause, precisely

```lean
def canonOkOf cb w w1 := acceptsD3 cb w1 && canonW cb w1 == w1 && decide (w1.length ≤ w.length)
def normalW cb w := let w1 := canonW cb w; w1 == w || !canonOkOf cb w w1
def proveW cb w  := let w1 := canonW cb w; if canonOkOf cb w w1 then w1 else w
```

* **What the prover emits.** `prove` emits `proveW cb w`: the canonical form `canonW cb w` when it is
  *usable* (`checkD3` accepts it, it is a fixed point of `canonW`, and it is no longer than `w`);
  otherwise — the "canon not usable" branch — the witness `w` exactly as given.
* **Why only normal bytes are accepted.** The verifier accepts `pb` only if `canonW pb = pb`, or
  `canonOkOf pb (canonW pb)` is false (`check_normal`). The second disjunct is the escape: it is
  taken only for a witness whose canonical form is not itself a valid, fixed, no-longer witness, i.e.
  only if `canonW` breaks `RelD3` on that witness. On every witness where `canonW` is correct, the
  canonical form is the *only* accepted encoding: a reordered, duplicated or padded variant `m` has
  `canonW m = canonW pb ≠ m` and a usable canonical form, so `normalW m` is false. That `canonW`
  preserves `RelD3` is **tested, not proved**: every positive of the public set (407) and of the
  held-out set takes the canonical branch, and 4 916 witness-freedom mutants of the 407 public proofs
  (values / entries / implicit reorder, duplicate, junk; the three ignored fields; code reorder,
  duplicate, junk, empty; code ↔ value moves) are all rejected. If a witness family existed where
  `canonW` broke `RelD3`, its members would be accepted as they are, and their variants could be
  accepted too: the escape is exactly where malleability would reappear, and it is what
  `ADVERSARIAL_PROOFS` probes. No lock-step proof that `canonW` preserves `RelD3` through the D2/WASM
  runtime is claimed (the D1/D2 `StoreCong` argument does not carry over: `Env.codeOf` and the WASM
  storage reads consult the store).
* **Completeness is not weakened.** `proveW_normal` / `check_proveW` (no hypothesis on `canonW`):
  for every `RelD3` witness `w`, `proveW cb w` is a `RelD3` witness, satisfies `normalW`, is no longer
  than `w`, and is accepted. With `DomainTier .d3a c = ∃ w, RelD3 c w ∧ |w| ≤ 64 MiB`
  (`maxWitnessChunk`), `verifierComplete` gives an accepted proof ≤ 64 MiB for every claim of the
  tier. The only witnesses the prover cannot turn into an accepted proof within the size cap are
  witnesses larger than 64 MiB (outside `DomainTier`; such a claim always has a smaller witness in
  practice, since `w.size` bounds the state witness by 8 MiB and the code bytes by 4 000 000). Cost
  of completeness: `prove` runs `checkD3` `2k + 1` times (`k` = candidate code blobs) and `verify`
  `k + 1` times on a canonical proof.

## Formal certificate

`ReexecV3D3.certificate : ArenaExpectedInst.expectedType` =
`AdmissionStatement (NearSpecV3.challengeParamsChunkWith .d3a profile fuel maxProofBytes red)
{ publicDigest, impl := .nativeTrusted binDigest toolchainId ReexecV3D3.Model.verifier }`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `native_decide`, `implemented_by`,
`extern`, `partial`, `unsafe` in the package.

| obligation | how |
|---|---|
| public digest | `public.bin` = approved `params.bin` (domain `D3a`) verbatim (`PublicBin.lean`), `decide +kernel` |
| `FORMAL_IMPL_CONNECTION` | `rfl` (native-lean, trusted edge) |
| `FORMAL_SEMANTIC_SOUNDNESS` / `COMPLETENESS` | backend `Aux := witness`, `B := Rel` |
| verifier completeness | `verifierComplete` via `proveW_normal` (above), any `maxProofBytes ≥ 64 MiB` |
| `FORMAL_CRYPTO_SOUNDNESS` | `DeterministicSound` (ε = 0): acceptance ⇒ `checkD3 (encode c) pb = .ok ()`; `statementSound` lifts it to `challengeSpecChunkTop` by `sound_lift` |

## Limitations

* Not succinct: the proof is the (normalised) witness, ≤ 182 KB on the public set.
* The residual freedom and the tested-not-proved canonicalisation above.
* `Rel_D3` is the cold-cache statement (spec/near-chunk-validation-d3.md §10.0): a warm-cache nearcore
  validator may accept witnesses without code blobs that `RelD3` rejects.
* The relation is a transcription of nearcore, difftested, not proved equal to it.

Results: `docs/e2e-results/v3-d3-reference/`.
