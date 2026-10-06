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
| `source/src/bin/{prepare,prove}.rs` | Rust, std only. `prepare` checks `near-arena-params-v3` (domain `D0`) and copies it to `public.bin`; `prove` checks the two format tags and writes `claim.bin = request.bin` (the claim IS the request in v3) and `proof.bin = witness.bin` |
| `source/src/bin/leanorder.rs` | build helper: the judge's trusted-module link order (`topo` in runners/formal-checker) |
| `source/lean-vendor/` | verbatim copies of the judge-trusted Lean modules of the challenge (`ArenaCore`, the 11 `NearSpec` modules, the 15 `NearSpecV3` modules listed in `runners/formal-checker/challenges/near-chunk-validation-d0.json`), used to compile `out/verify` offline. Refresh with `source/verifier/sync-vendor.sh <frozen commit>`; digests pinned in `dependency-locks/lean-vendor.sha256` |
| `source/verifier/` | dev Lake project (certificate against `judge-local/`), the judge's `main` wrapper template (verbatim), `sync-vendor.sh` |
| `formal/ReexecV3D0/` | Lean: verifier model, size bound, obligations, public tape, certificate |
| `judge-local/` | **local emulation** of the judge-generated `ArenaExpected` / `ArenaExpectedInst` modules, for development only (the judge renders `spec/lean/judge/ExpectedV3D0.native-lean.lean.template` itself) |
| `build-recipe/build.sh` | offline reproducible build of `out/{prepare,prove,verify}` |

## Proof format

`proof.bin` = `witness.bin` verbatim (`near-arena-witness-v3`: `bytes
"near-arena-witness-v3" ‖ bytes state_witness ‖ Vec<bytes> contract_code`). On
every D0 witness it is at most 8 388 641 bytes (proved, below); the public
fixtures produce 1.5–19 KB.

## Verifier

```lean
def check (cb pb : Bytes) : Bool :=
  match WfClaim.decode cb with
  | none => false
  | some c => decide (RelD0 c.encode pb)
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
| verifier completeness | the honest proof is the witness `w`; `WfClaim.decode_encode` (the proved codec round trip of `NearSpecV3.ChallengeV3`) and `decide_eq_true`; size: `relD0_witness_length : RelD0 cb w → w.length ≤ 8 388 641` (`Size.lean`, proved over the trusted parsers: `checkD0` accepts only an empty code list and `|state_witness| ≤ 8 MiB`, and `decodeWitnessFile` consumes exactly `33 + |state_witness|` bytes) ≤ `maxProofBytes` = 64 MiB |
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
* Public fixtures (`oracle/fixtures/v3/arena-public`): all 80 positives
  (64 honest D0 chunks + 16 nearcore-accepted mutants) proved and accepted; all
  121 rejection cases (59 honest out-of-D0 chunks, 62 nearcore-rejected mutants)
  rejected by `verify`.

## Limitations

* The proof is not succinct: it carries the full witness (re-execution family).
  Verify time on the fixtures is 0.01–0.32 s (Reed–Solomon (33,100) cases are
  the slowest); it is not scored.
* `prove` decides nothing; on a false or out-of-domain claim it still emits a
  proof, which `verify` rejects.
