# formal-core — `ArenaCore`

This Lean 4 package defines the arena's admission theorem. The judge
builds the theorem type `ArenaCore.AdmissionStatement ch art` from the frozen
challenge and the exact artifact digests, and every candidate certificate
must have that type. The design and its limitations are in
[`docs/FORMAL_INTERFACE.md`](../docs/FORMAL_INTERFACE.md). The bytecode
interpreter is specified in [`docs/INTERP_SPEC.md`](../docs/INTERP_SPEC.md).

* Toolchain: `leanprover/lean4:v4.34.1` (`lean-toolchain`). It also builds on v4.34.0.
* Dependencies: none (no Mathlib).
* Build: `lake build` (about 4 s from clean). The build includes the toy certificate and pinned tests.

## Layout

| module | contents |
|--------|----------|
| `ArenaCore.Bytes` | `Bytes := List UInt8`, big/little-endian codecs, hex (diagnostics) |
| `ArenaCore.SHA256` | FIPS 180-4 SHA-256 on `Nat` words, kernel-reducible; `sha256_length` |
| `ArenaCore.Relation` | `ChallengeSpec` (Claim, Witness, `Rel`, `Domain`, claim codec), `InLang` |
| `ArenaCore.Backend` | `Backend` (`B : Claim → Aux → Prop`), `SemSound`, `SemComplete` |
| `ArenaCore.Interp` | NPAI v1 interpreter: syntax, semantics (`exec`, `runWith`, `run`, `runOut`), image codec (`decode`/`encode`), `interpVerify` |
| `ArenaCore.InterpLemmas` | symbolic-execution toolkit (memory, Bool comparisons, `cont`) |
| `ArenaCore.Verifier` | `Verifier`, hash-parametric `OracleVerifier`/`OracleProver`, `DeterministicSound`, `VerifierComplete`, `ProverComplete` |
| `ArenaCore.Security.OracleComp` | query trees, `QueryBound`, `simulate`, coin oracle |
| `ArenaCore.Security.Prob` | tapes, counting, `PrLE` |
| `ArenaCore.Security.Adversary` | `CoinAdversary` |
| `ArenaCore.Assumptions` | `AssumptionId`, `Sha256CollisionResistant` (governed) |
| `ArenaCore.Security.CR` | explicit reduction to SHA-256 collisions: `CRReduction`, `CRSecure`, `secure_of_sound` |
| `ArenaCore.Security.ROM` | lazy random oracle and the ROM soundness game `RomSound` |
| `ArenaCore.Security.ROMLemmas` | lazy-oracle invariant, tape counting, `rom_guess_bound` |
| `ArenaCore.Admission` | `ChallengeParams`, `ArtifactDescription`, `VerifierImpl` routes, `CryptoSound`, `Obligations`, **`AdmissionStatement`**, `endToEnd` |
| `ArenaCore.Sanity` | non-vacuity theorems (accept-all / reject-all verifiers cannot pass) |
| `Toy.*` | worked example (**not NEAR**): spec, bytecode, judge file (`Toy/Artifacts.lean`), certificate (`Toy.certificate : ToyJudge.Expected`) |
| `ArenaCoreTests.*` | SHA-256 vectors (kernel-checked "abc"), NPAI vector regression pin |
| `InterpRef.lean` | `lake exe arena-interp-ref` (differential-testing oracle for the Rust interpreter) |
| `vectors/npai-v1.json` | committed NPAI vector suite (regenerate: `lake exe arena-interp-ref vectors vectors/npai-v1.json`) |
| `negative/` | certificates that must FAIL the checker, plus `check_negative.sh` |

## For candidates

```toml
# formal/lakefile.toml (pin the commit given by the challenge)
[[require]]
name = "ArenaCore"
git = "<arena repo>"
rev = "<pinned commit>"
subDir = "formal-core"
```

Your certificate is `theorem certificate : Judge.Expected := …`, where the
judge generates `Judge.Expected` (see `Toy/Artifacts.lean` for the shape).
For the interpreter route, your proof is about `ArenaCore.Interp` running
**your exact bytecode image**. `Toy/BytecodeProofs.lean` shows how to
symbolically execute a program with `simp` and the `InterpLemmas` toolkit, and
how to discharge completeness by kernel evaluation (`decide +kernel`).
`native_decide` is rejected.

## Checks

```sh
lake build                          # core + tests + toy certificate
lake exe arena-interp-ref vectors /tmp/v.json
negative/check_negative.sh          # positive control passes, 11 negatives rejected
```
