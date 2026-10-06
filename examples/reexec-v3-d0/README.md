# reexec-v3-d0: reference candidate (baseline) for v3 D0

The reference candidate for **`near/pv86/chunk-validation/v0`, domain D0**
(challenge `near-chunk-validation-d0`; statement `spec/near-chunk-validation-v0.md`,
formats `spec/claim-v3.md`). Backend family **re-execution witness**: the proof is
the witness itself (the real nearcore `ChunkStateWitness` bytes the chunk producer
emitted), and the verifier decides the Lean relation `NearSpecV3.RelD0` on the
claim and that witness. It is the v3 analogue of `examples/reexec-witness` (v1).

## Layout

| path | what |
|---|---|
| `source/src/bin/{prepare,prove}.rs` | Rust, std only. `prepare` checks `near-arena-params-v3` (domain `D0`) and copies it to `public.bin`; `prove` writes `claim.bin = request.bin` (the claim IS the request in v3) and `proof.bin` = the **canonical** witness file (below); it refuses (exit 2) a witness whose D0 layout it cannot walk |
| `source/src/bin/leanorder.rs` | build helper: the judge's trusted-module link order (`topo` in runners/formal-checker) |
| `source/lean-vendor/` | verbatim copies of the judge-trusted Lean modules of the challenge (`ArenaCore`, the 11 `NearSpec` modules, the 15 `NearSpecV3` modules listed in `runners/formal-checker/challenges/near-chunk-validation-d0.json`), used to compile `out/verify` offline. Refresh with `source/verifier/sync-vendor.sh <frozen commit>`; digests pinned in `dependency-locks/lean-vendor.sha256` |
| `source/verifier/` | dev Lake project (certificate against `judge-local/`), the judge's `main` wrapper template (verbatim), `sync-vendor.sh` |
| `formal/ReexecV3D0/` | Lean: verifier model, size bound, obligations, public tape, certificate |
| `judge-local/` | **local emulation** of the judge-generated `ArenaExpected` / `ArenaExpectedInst` modules, for development only (the judge renders `spec/lean/judge/ExpectedV3D0.native-lean.lean.template` itself) |
| `build-recipe/build.sh` | offline reproducible build of `out/{prepare,prove,verify}` |

## Proof format (canonical witness)

`proof.bin` = the witness file (`near-arena-witness-v3`: `bytes
"near-arena-witness-v3" ‖ bytes state_witness ‖ Vec<bytes> contract_code`, no code)
in **canonical form**: the three fields nearcore's chunk validator never reads are
fixed — the chunk header's `height_included` = 0, its signature = ED25519 with 64
zero bytes, every `ChunkStateTransition.block_hash` = 32 zero bytes
(`formal/ReexecV3D0/CanonDefs.lean`, `canonicalW`). Everything else is the producer's
bytes. On every D0 witness it is at most 8 388 641 bytes (proved, below); the public
fixtures produce 1.5–118 KB.

Why: the first live run of this reference (proof = raw witness) was REJECTED by
`ADVERSARIAL_PROOFS` — a bit flipped in the signature gave a second accepted proof of
the same claim (docs/e2e-results/v3-d0-reference/). Exhaustive single-bit flips of
two canonical proofs (1 565 B and 5 214 B, with an implicit transition): 0 accepted.

## Verifier

```lean
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => canonicalW pb && decide (RelD0 c.encode pb)
```

`ReexecV3D0.Model.verifier` (`formal/ReexecV3D0/Model.lean`) ignores the public
tape and the hash oracle. Route **`native-lean`**: the judge compiles the model
with the governed Lean compiler and its own `main` wrapper; `build.sh`
replicates that build step for step (`lean -c` on every trusted module in the
judge's topological order over the three trusted packages, the model, the
wrapper verbatim, `leanc -c -O3 -DNDEBUG`, one `leanc -o` link), so `out/verify`
is byte-identical to the judge's build (checked by `ARTIFACT_BINDING`). The
binary ↔ model edge is **trusted** (Lean compiler and runtime in the TCB).

## Formal certificate

`ReexecV3D0.certificate : ArenaExpectedInst.expectedType` =
`AdmissionStatement (NearSpecV3.challengeParamsWith profile fuel maxProofBytes red)
{ publicDigest, impl := .nativeTrusted binDigest toolchainId ReexecV3D0.Model.verifier }`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
`native_decide`, `implemented_by`, `extern`, `partial`, `unsafe`.

| obligation | how it is discharged |
|---|---|
| public digest | `public.bin` = approved `params.bin` verbatim (`PublicBin.lean`), `sha256` by `decide +kernel` |
| `FORMAL_IMPL_CONNECTION` | `rfl`: the model in the statement *is* `ReexecV3D0.Model.verifier` (trusted edge) |
| `FORMAL_SEMANTIC_SOUNDNESS` / `COMPLETENESS` | backend `Aux := witness bytes`, `B := Rel` |
| verifier completeness | the honest proof is the canonical form `w'` of the witness `w`: `relD0_canonical : RelD0 cb w → ∃ w', RelD0 cb w' ∧ canonicalW w' ∧ |w'| ≤ |w|` (`Canon.lean`), built from (a) context-freeness of every trusted witness parser (`CF.lean`: a parser that accepts `pre ++ r` leaving `r` accepts `pre ++ r'` leaving `r'`), (b) a canonical re-parse (`canon_exists`: the bytes with the ignored fields replaced decode to the same witness with zeroed block hashes), (c) `checkD0_norm` (`Norm.lean`: `checkD0` never reads a transition block hash); then `WfClaim.decode_encode` (the proved codec round trip of `NearSpecV3.ChallengeV3`) and `decide_eq_true`; size: `relD0_witness_length : RelD0 cb w → w.length ≤ 8 388 641` (`Size.lean`) ≤ `maxProofBytes` = 64 MiB |
| `FORMAL_CRYPTO_SOUNDNESS` | **`DeterministicSound`** (ε = 0, no assumption): acceptance ⇒ `RelD0 (encode c) pb` for the decoded claim |

No collision-resistance assumption is needed for soundness: `RelD0` is stated
over `ArenaCore.sha256` values (block hashes, `chunk_headers_root`, receipt-proof
paths, state roots), which the verifier recomputes from the explicit witness.
Collision resistance is what makes `RelD0` meaningful about the real chain
(spec §2.1: section B of the claim is a function of `prev_block_hash`), not a gap
between verifier and relation.

**What the certificate does not cover** (stated, not hidden): the relation is
the Lean transcription of nearcore's validator; its faithfulness to nearcore is
*tested* (3-way difftest of spec §10, the oracle's labels on every judge case),
not proved. Trusted claim facts (section C, `epoch_id`, `protocol_version`,
`chain_id`) are only consistency-checked (spec/claim-v3.md §2.4).

## Checks

* Real formal checker (`runners/formal-checker`, dev bwrap sandbox, config
  `near-chunk-validation-d0.json`, clean export of `formal-core` + `spec/lean`):
  `FORMAL_SEMANTIC_SOUNDNESS`, `FORMAL_SEMANTIC_COMPLETENESS`,
  `FORMAL_CRYPTO_SOUNDNESS`, `FORMAL_IMPL_CONNECTION`, `AXIOM_AUDIT`,
  `ARTIFACT_BINDING` all **PASS**; leanchecker, nanoda, lean4lean, arena-audit
  and the NDJSON audit accept. Judge-built `verify` = `build.sh` output.
* Public fixtures (`oracle/fixtures/v3/arena-public`): all 78 positives
  (64 honest D0 chunks + 14 nearcore-accepted mutants) proved and accepted; of the
  121 rejection cases 49 are refused by `prove` and 72 rejected by `verify`.
* Worker pipeline (`runners/worker/tests/near_v3.rs`, bwrap-dev): all stages pass,
  164 hostile inputs rejected including the structure-aware `v3-ignored-fields`
  mutants; the pre-canonical version (hostile case `near-v3-malleable-witness`) fails
  `ADVERSARIAL_PROOFS` with `HOSTILE_PROOF_ACCEPTED`.

## Limitations

* The proof is not succinct: it carries the full witness (re-execution family).
  Verify time on the fixtures is 0.01–0.32 s (Reed–Solomon (33,100) cases are
  the slowest); it is not scored.
* `prove` decides nothing; on a false or out-of-domain claim it still emits a
  proof (unless it cannot walk the witness layout), which `verify` rejects.
* Canonical form covers the three validator-ignored fields. Other freedoms of
  nearcore's lenient decoding (duplicate or unsorted `source_receipt_proofs` keys,
  unreferenced `base_state` values) are not normalised: they are insertions or
  reorderings, not single-byte changes, and the reference prover never produces them.
