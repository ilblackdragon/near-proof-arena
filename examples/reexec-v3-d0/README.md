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
| `source/src/bin/prepare.rs` | Rust, std only: checks `near-arena-params-v3` (domain `D0`) and copies it to `public.bin` |
| `source/prover/ProveMain.lean` | `prove` (Lean, linked with the same compiled trusted + model modules as `verify`): writes `claim.bin = request.bin` (the claim IS the request in v3) and `proof.bin` = the witness file in **normal form**, computed by the verifier model's own normaliser `ReexecV3D0.normSW` (below); it refuses (exit 2) a witness the normaliser cannot process (no `keysD0`: false/out-of-domain claim, undecodable witness, contract code) |
| `source/src/bin/leanorder.rs` | build helper: the judge's trusted-module link order (`topo` in runners/formal-checker) |
| `source/lean-vendor/` | verbatim copies of the judge-trusted Lean modules of the challenge (`ArenaCore`, the 11 `NearSpec` modules, the 15 `NearSpecV3` modules listed in `runners/formal-checker/challenges/near-chunk-validation-d0.json`), used to compile `out/verify` offline. Refresh with `source/verifier/sync-vendor.sh <frozen commit>`; digests pinned in `dependency-locks/lean-vendor.sha256` |
| `source/verifier/` | dev Lake project (certificate against `judge-local/`), the judge's `main` wrapper template (verbatim), `sync-vendor.sh` |
| `formal/ReexecV3D0/` | Lean: verifier model, size bound, obligations, public tape, certificate |
| `judge-local/` | **local emulation** of the judge-generated `ArenaExpected` / `ArenaExpectedInst` modules, for development only (the judge renders `spec/lean/judge/ExpectedV3D0.native-lean.lean.template` itself) |
| `build-recipe/build.sh` | offline reproducible build of `out/{prepare,prove,verify}` |

Before the normal form (live runs 1–2) `prove` was Rust (`source/src/bin/prove.rs`);
those versions are the permanent hostile cases `near-v3-malleable-witness` and
`near-v3-lenient-witness` (`adversarial/hostile-submissions/`).

## Proof format (normal form)

`proof.bin` = the witness file (`near-arena-witness-v3`: `bytes
"near-arena-witness-v3" ‖ bytes state_witness ‖ Vec<bytes> contract_code`, no code)
whose state witness is in **normal form** — every degree of freedom that nearcore's
validator (and so `RelD0`) leaves is fixed:

| freedom (nearcore) | normal form | Lean |
|---|---|---|
| chunk header `height_included`, chunk signature, every `ChunkStateTransition.block_hash`: never read | 0 / ED25519 + 64 zero bytes / 32 zero bytes | `CanonDefs` |
| `source_receipt_proofs: HashMap<ChunkHash, ReceiptProof>` decoded leniently: any entry order, a duplicate key keeps the **last** value | one entry per key (the last), increasing byte order of the key; each entry's bytes are the producer's | `normEntries`, `normPairs` |
| every `PartialState::TrieValues` (`base_state`) is a `Vec` used as a hash-indexed store: any order, duplicates, values never looked up | exactly the values the relation looks up while building its partial tries (`qFor`, a mirror of `NearSpecV3.buildFor` recording every `storeGet`), deduplicated, increasing byte order — main transition: builds at the main pre-state root with `[keyBufferedIdx]` and `mainKeys` (`keysD0`); implicit transition *i*: build at the previous post-state root with `[keyDelayedIdx, keyBwState]` | `qFor`, `normVals`, `normMain`, `normT` |

Everything else is the producer's bytes (the header and inner, the receipts and
merkle paths inside each entry, the applied-receipts hash). Audit of the remaining
decoded fields: the counts (`transactions`, `new_transactions`, contract code) must be 0
in D0; every other field of `ChunkStateWitness` is either compared to the claim
(`epoch_id`, chunk header inner) or hashed / read by the relation (receipts, proofs,
roots), so a different value changes the verdict, not just the bytes; the only
remaining encoding choices are the three above.

`normSW K R sw` (`NormBytesDefs.lean`, part of the verifier model) computes the
normal-form bytes; the verifier accepts only a state witness that is a **fixed point**
of it (`normalW`). Honest nearcore witnesses already carry exactly the read set; on the
public fixtures the normal form changes only the ignored fields and the order of
values (same length), except the oracle's 4 deliberately lenient positives
(`*-w.base_state.extra_junk`, `*-w.dup_key_last_good`), which shrink by 18–294 bytes.

## Verifier

```lean
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => normalW c.encode pb && decide (RelD0 c.encode pb)
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
| verifier completeness | the honest proof is the normal form `w'` of the witness `w`, computed by the prover's normaliser: `relD0_normal : RelD0 cb w → ∃ w', RelD0 cb w' ∧ normalW cb w' ∧ |w'| ≤ |w|` (`NormalForm.lean`; `w' = wrapW c` with `normSW K R sw = .ok c`, `keysD0 cb w = .ok (K, R)`), built from (a) context-freeness of every trusted witness parser (`CF.lean`), (b) parse inversion and the byte-level normaliser (`NormBytes.lean`, `normSW_spec`: on every decodable `sw`, `normSW` succeeds, its output decodes to `normW K R s`, is no longer, and is a fixed point), (c) `checkD0_normal` / `keysD0_normal` (`Normal.lean`: `checkD0` and `keysD0` evaluated in lockstep on `s` and on `normW K R s` — `lookupLast` on the deduplicated sorted entries, the partial tries built from the read set (`TrieQ.lean`: `buildFor` only consults `qFor` hashes), the smaller `base_state`); `keysD0_of_checkD0` (it is a verbatim prefix); then `WfClaim.decode_encode` and `decide_eq_true`; size: `relD0_witness_length : RelD0 cb w → w.length ≤ 8 388 641` (`Size.lean`) ≤ `maxProofBytes` = 64 MiB |
| only normal bytes are accepted | `normalW_sound`: `normalW cb w` ⇒ `normSW K R sw = .ok sw` (byte-exact fixed point); `normalW_fixed`: with `RelD0`, the decoded state witness `s` satisfies `normW K R s = s`; idempotence `normW_idem` (`Normal.lean`) |
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
  121 rejection cases 84 are refused by `prove` (no `keysD0`) and 37 rejected by
  `verify`, 0 accepted.
* Worker pipeline (`runners/worker/tests/near_v3.rs`, bwrap-dev): all stages pass,
  including `ADVERSARIAL_PROOFS` with the structure-aware `v3-ignored-fields` and
  `v3-witness-freedoms` mutants; judge-built `verify` = `build.sh` output
  (`sha256:19ee48ed…`). The pre-canonical version (hostile case
  `near-v3-malleable-witness`) and the canonical-only version (`near-v3-lenient-witness`)
  both fail `ADVERSARIAL_PROOFS` with `HOSTILE_PROOF_ACCEPTED`.

## Limitations

* The proof is not succinct: it carries the full witness (re-execution family).
* `prove` is the Lean normaliser (`keysD0` + `normSW`, compiled native code over
  `List UInt8` data): on the public fixtures it takes 0.02–0.64 s per case, against
  ~1 ms for the earlier Rust prover that only zeroed fields; `keysD0` (the claim-segment
  walk and receipt pre-validation up to the main trie build, verbatim from `checkD0`)
  dominates. Since the score is prove time, the reference now scores far below the
  frozen baseline (the canonical-only package `sha256:63618259…`). A fast native
  normaliser that reproduces `qFor`/`keysD0` byte-exactly is possible but would be an
  untrusted re-implementation (checked only by the verifier's fixed-point test).
* `verify` additionally runs `keysD0` + `normSW` (+~10 % over `RelD0` alone on the
  public fixtures).
