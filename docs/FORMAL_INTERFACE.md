# Formal interface: the admission theorem

Owner: formal-core lane. Code: `formal-core/` (Lake package `ArenaCore`).
Companion documents: `docs/INTERP_SPEC.md` (the NPAI bytecode interpreter),
`formal-core/README.md` (layout, build), `formal-core/negative/README.md`
(the rejection suite).

The invariant from `docs/CONTRACTS.md` drives everything here: **candidates
control how proofs are produced and checked internally; the arena controls
what must be proved, which assumptions are allowed, and which exact
artifacts are certified.** In Lean terms, the candidate supplies a *term*;
the judge constructs its *type*, `AdmissionStatement ch art`, from the
frozen challenge `ch` and the digests of the artifacts the judge itself
built (`art`). Nothing in that type is written by the candidate.

## 1. Toolchain and dependencies

* **Lean `leanprover/lean4:v4.34.1`**, the latest stable release when this was
  written (2026-10-03). Compared with v4.34.0 it only changes runtime
  reference counting (memory-safety fixes in compiled code, which matter
  because the checker runs on hostile inputs). The kernel is unchanged. The
  package also builds unchanged on v4.34.0, the Mathlib/ArkLib/VCVio release
  tag, so a challenge that must allow Mathlib can pin v4.34.0 without
  touching formal-core. The spec lane (`spec/lean`) is also on v4.34.1.
  `docs/research/checker-recommendations.md` was not available while this
  was written; reconcile the pin with it when it lands.
* **No Mathlib, and no dependencies at all.** The trusted core
  (`ArenaCore`) is about 2.1k lines of plain Lean 4 core. A clean
  `lake build` (core, tests, toy certificate) takes **3.9 s wall time on
  32 cores and 0.6 GB peak RSS**. That keeps the checker image small and
  re-checks fast, and the part of the TCB that a reviewer must read is just
  this package. No
  concrete need for Mathlib came up. Probability is counting over finite
  tapes (`Nat` arithmetic and `List.countP`), and the byte, word and SHA
  arithmetic is on `Nat`. Candidates *may* use Mathlib in their own proofs
  if the challenge's `allowed_imports` lists it. ArenaCore is importable
  alongside Mathlib because it defines nothing in Mathlib's namespaces.
* Axioms used by every main theorem: a subset of
  `[propext, Classical.choice, Quot.sound]` (§10). Nothing uses `sorry`,
  `axiom`, `native_decide`, `implemented_by`, `extern` or `partial` in a proof
  path. `partial` appears only in the reference executable's CLI parser.

## 2. The theorem shape

```lean
-- ArenaCore/Admission.lean
def AdmissionStatement (ch : ChallengeParams) (art : ArtifactDescription) : Prop :=
  ∃ (pub : Bytes) (v : OracleVerifier),
    sha256 pub = art.publicDigest ∧                 -- (P) public artifacts pinned
    art.impl.Connection ch.verifyFuel v ∧           -- FORMAL_IMPL_CONNECTION
    ∃ bk : Backend ch.spec, Obligations ch pub v bk

structure Obligations ch pub v bk : Prop where
  semSound         : bk.SemSound                    -- FORMAL_SEMANTIC_SOUNDNESS
  semComplete      : bk.SemComplete                 -- FORMAL_SEMANTIC_COMPLETENESS
  verifierComplete : VerifierComplete ch.spec v.deployed pub ch.maxProofBytes
  cryptoSound      : CryptoSound ch pub v bk        -- FORMAL_CRYPTO_SOUNDNESS
```

The parameters, all fixed by the judge:

| Lean | meaning | arena source |
|------|---------|--------------|
| `ch.spec : ChallengeSpec` | `Claim`, `Witness`, `Rel` (= `NearRelation`), input `Domain`, canonical `decodeClaim`/`encodeClaim` + round-trip law | `semantic_scope.formal_spec`, `claim_encoding` (spec lane: `NearSpec.WfClaim.*`) |
| `ch.profile : SecurityProfile` | `model` (standard / randomOracle), `targetBits`, `allowedAssumptions`, `maxHashQueriesLog2`, `maxProverQueriesLog2` | `security_profile` |
| `ch.verifyFuel` | NPAI fuel per `verify` call | `resource_limits` (proposed field) |
| `ch.maxProofBytes` | honest proof size bound | `resource_limits` |
| `ch.maxReductionFuel` | cost cap for explicit security reductions | security profile (proposed field) |
| `art.publicDigest` | `sha256(public.bin)` from the judge-run `prepare` | judge build |
| `art.impl` | `.interp bytecodeDigest` or `.nativeTrusted binaryDigest toolchainId model` | judge build + candidate manifest |

Digests are *data* in the statement (literal 32-byte lists in the
judge-generated file). A certificate for one artifact therefore cannot be
replayed for another: changing a single byte of the verifier changes the
type (`negative/09_stale_digest.lean`).

Two things follow from the statement and are proved
(`AdmissionStatement.endToEnd`, `Obligations.endToEnd`): completeness of the
deployed verifier, and soundness against the challenge relation itself.
Soundness comes in one of three forms (deterministic, CR-relative, ROM-bounded)
for the language `S.InLang cb := ∃ c, decodeClaim cb = some c ∧ ∃ w, Rel c w`,
with no backend vocabulary left in it.

## 3. The obligations

### 3.1 Public artifacts (P)

`sha256 pub = art.publicDigest`. The certificate's statements are about the
bytes `pub` that the deployed verifier reads as its public tape. SHA-256 is
evaluated by the kernel (`decide +kernel`). It costs about 0.15 s per 64-byte
block, so kilobyte-scale public data is fine and megabyte-scale keys are not
(§11).

### 3.2 Semantic soundness and completeness (backend layer)

A backend is described only by `Backend S := { Aux : Type, B : S.Claim → Aux → Prop }`.
The contract has no AIR, R1CS or trace vocabulary; any architecture can
choose `Aux` and `B`.

* `SemSound  : ∀ c aux, B c aux → ∃ w, Rel c w`. There is no precondition.
* `SemComplete : ∀ c w, Domain c → Rel c w → ∃ aux, B c aux`.

Anti-vacuity:

* `Domain` is a field of `ChallengeSpec` (judge) and appears only as a
  precondition of completeness.
* Soundness is never restricted to the domain, because an adversary may submit
  any bytes.
* Preconditions cannot mention the conclusion, because they are fixed
  judge-side definitions.
* `B = False` fails completeness as soon as one true in-domain claim exists,
  and `B = True` fails soundness as soon as one false claim exists
  (`Sanity.backend_false_not_complete`, `Sanity.backend_true_not_sound`).

### 3.3 Verifier completeness

`VerifierComplete S v pub maxProofBytes : ∀ c w, Domain c → Rel c w → ∃ pb,
|pb| ≤ maxProofBytes ∧ v pub (encodeClaim c) pb = true`.

This is about the **deployed** verifier on the **canonical** claim encoding.
It is the obligation that rules out the always-rejecting verifier, which
satisfies every soundness notion
(`Sanity.rejectAll_not_complete`, `Toy.toy_rejectAll_not_complete`). For
the interpreter route it includes "accepts within `verifyFuel`".

### 3.4 Cryptographic soundness

```lean
def CryptoSound ch pub v bk : Prop :=
  DeterministicSound bk.InLang v.deployed pub ∨
  match ch.profile.model with
  | .standard     => sha256CollisionResistance ∈ allowed ∧
                     ∃ r : CRReduction, r.fuel ≤ ch.maxReductionFuel ∧
                       CRSecure r bk.InLang v.deployed pub
  | .randomOracle => sha256RandomOracle ∈ allowed ∧
                     ∃ P : OracleProver ch.spec, ProverComplete ch.spec v P pub ch.maxProofBytes ∧
                     ∃ tapeLen num den, num * 2^targetBits ≤ den ∧
                       RomSound ch.spec bk.InLang v P pub
                         (2^maxHashQueriesLog2) (2^maxProverQueriesLog2) tapeLen num den
```

There are three cases, kept apart on purpose.

**(i) Deterministic relation correctness.** `DeterministicSound L v pub :=
∀ cb pb, v pub cb pb = true → L cb`. Every accepted claim is true, with no
probability and no assumption. Re-execution backends whose proof contains
the witness use this, at ε = 0. It is a statement about the deterministic
function `verify` and is never mixed up with (ii) or (iii).

**(ii) Standard model, explicit reduction to SHA-256 collisions.** SHA-256
is a fixed keyless function. "No efficient adversary finds collisions" is
false as a formal statement, because a constant adversary that prints a
collision exists. The theorem therefore uses Rogaway's "human ignorance"
formulation.

* The certificate supplies a `CRReduction`, an **NPAI bytecode program plus a
  fuel bound** `≤ ch.maxReductionFuel`. It must not be an arbitrary Lean
  function: a total Lean function could brute-force a collision (one exists by
  pigeonhole), which would make *any* verifier "secure". A fuel-bounded
  program cannot, so the composed finder costs `cost(A) + fuel`.
* `CRReduction.Sound`: for **every** `(claim, proof)` such that the deployed
  verifier accepts a claim outside the language, the reduction's outputs
  `(x, y)` satisfy `x ≠ y ∧ sha256 x = sha256 y`. This is pointwise, so it
  covers every adversary: adaptive or not, and with any auxiliary oracle it
  can simulate, such as honest proofs for statements whose witnesses it knows.
* `CRSecure` is the probabilistic statement in the type. For every
  randomized adversary `A` (a `CoinAdversary`, an oracle program over a coin
  oracle with an explicit tape length and alphabet) and every bound
  `num/den`: if `Sha256CollisionResistant (r.finder pub A) num den` holds,
  then `Pr[A produces a bad acceptance] ≤ num/den`. The hypothesis is
  supplied by the judge's type and is the governed assumption `sha256_cr`,
  instantiated at the explicitly composed finder. The bound has tightness 1:
  `secure_of_sound` derives it from pointwise soundness through monotonicity
  of counting.

So the concrete bound is *relative*: Adv_bad(A) ≤ Adv_coll(r∘A), and r∘A
costs at most `cost(A) + maxReductionFuel` NPAI fuel. Governance interprets
`sha256_cr` at the profile's target. A reduction could only make a bad
verifier "secure" by having a SHA-256 collision hard-coded. None is known,
and finding one would retire the assumption.

**(iii) Random-oracle model, game against the deployed transcript.** This
case serves Fiat–Shamir and Merkle-hash backends. An interactive-protocol
theorem alone does not suffice; the ROM game runs **the deployed
non-interactive verifier**:

* Every verifier model is *hash-parametric* (`OracleVerifier.run : ∀ σ,
  HashOracle σ → σ → pub → claim → proof → Bool × σ`). The deployed verifier
  is `run shaOracle ()`. For the interpreter route, `interpOracleVerifier`
  derives `run` from the bytecode, so the game literally executes the
  candidate's image. Every protocol-hash opcode `ROHASH` (deployed as
  `SHA-256("NPAI-RO-v1" ‖ m)`) is answered by the oracle, while the `SHA256`
  opcode stays real SHA-256 because statement-level hashing must keep meaning
  what the challenge relation means (`Verifier.lean`, `Interp.runWith`,
  `INTERP_SPEC.md` §4).
* The oracle is a **lazily sampled random function** on a finite tape of
  `tapeLen` symbols in `[0, 2^256)`. The i-th distinct query gets the
  big-endian encoding of the i-th symbol, and repeated queries are answered
  consistently. **Running out of tape counts as an adversary win**, so the
  candidate gains nothing from a short tape.
* Adversaries are `OracleComp (romSpec W)` query trees with `hash x` and
  `prove cb w` queries, under explicit budgets `QueryBound hashWeight A
  2^maxHashQueriesLog2` and `QueryBound proveWeight A 2^maxProverQueriesLog2`.
  This handles adaptivity and repeated proofs. `prove` is answered by the
  candidate's honest prover `P` (itself hash-parametric, so its hash calls go
  through the same oracle), and only on true statements. `P` is pinned by
  `ProverComplete`: for *every* hash function, honest proofs of in-domain true
  claims are within `maxProofBytes` and accepted. A trivial prover is
  therefore impossible.
* `RomSound … tapeLen num den : ∀ A within budgets, Pr_tape[win] ≤ num/den`,
  where win = overflow or (verifier accepts ∧ claim ∉ language). The judge's
  type additionally demands `num * 2^targetBits ≤ den`. Probabilities are
  `PrLE n R E num den := 0 < den ∧ #{t ∈ [0,R)^n | E t} · den ≤ num · R^n`.
  The `0 < den` conjunct is essential, because `num/0` would make every bound
  trivially true. The target check is kernel `Nat` arithmetic: the candidate
  proves it with `decide`, never `native_decide`.
* The game is shown to be usable as well as stated:
  `Security.rom_guess_bound` proves that a q-query adversary hits a fixed
  oracle value with probability ≤ (q+1)/2^256. That is the basic step of
  Fiat–Shamir soundness. The proof uses the lazy-oracle invariant
  (`LazyInv.simulate`) and the tape-counting lemmas
  (`count_coord`, `tape_hit_bound`). `Sanity.acceptAll_not_romSound` shows
  the game is not vacuous: the always-accepting verifier fails every bound
  `< 1`.

## 4. Implementation connection

`art.impl.Connection fuel v` decides *which* verifier the obligations are
about. The candidate never chooses it freely.

**(a) Approved interpreter (`.interp d`), status *checked*.**
`∃ code, sha256 code = d ∧ v = interpOracleVerifier code fuel`. The
certificate exhibits the bytecode, the kernel checks its digest, and every
other obligation is about `Interp.interpVerify code fuel`, which decodes and
runs that exact image (`interpOracleVerifier_deployed`). The executed
verifier is the judge's Rust NPAI interpreter running the file with digest
`d`. The TCB for this edge is therefore the interpreter's agreement with
`ArenaCore.Interp`, which is differentially tested (`INTERP_SPEC.md` §6),
plus SHA-256 binding: two images with one digest would be a collision. No
compiler is involved. The Toy certificate proves its verifier and reduction
correct by symbolic execution of `Interp.exec` (`Toy/BytecodeProofs.lean`).

**(b) Native with a governed trusted toolchain (`.nativeTrusted binDigest
toolchainId model`), status *trusted*.** The obligations are proved about the
Lean `model : OracleVerifier`. The claim that the native binary with
`binDigest`, built reproducibly by toolchain `toolchainId`, implements
`model` is **not** a Lean fact. `VerifierImpl.status` returns `.trusted`, and
the evidence graph must render this edge as `trusted` (never `checked`)
together with the toolchain id. A certificate for route (b) does not
type-check against a route-(a) artifact description
(`negative/11_wrong_route_native.lean`).

## 5. Assumptions (governed, judge-supplied)

| id | Lean declaration | used as |
|----|------------------|---------|
| `sha256_cr` | `ArenaCore.Assumptions.Sha256CollisionResistant (F : CoinAdversary (Bytes × Bytes)) (num den : Nat) : Prop` | hypothesis inside `CRSecure`, instantiated at `r.finder pub A` |
| `sha256_rom` | `ArenaCore.AssumptionId.sha256RandomOracle`, which authorises the game `ArenaCore.Security.RomSound` | a model choice, not a `Prop`: the ROM is uninstantiable in general and has no honest propositional form |

`security/assumptions/*.json` → `lean_decl` should point at these names.
(The example in `arena-types` says `Arena.Assumptions.…`; the package
namespace is `ArenaCore`.) Candidates cannot add assumptions. Assumptions
reach the proof only as hypotheses inside the judge-built type. Any
candidate `axiom` appears in the transitive axiom set and fails `AXIOM_AUDIT`
(`negative/02_extra_axiom.lean`). A candidate-added premise changes the
theorem's type and fails `THEOREM_TYPE_MISMATCH` (`negative/04`, `05`).

## 6. Security framework summary (`ArenaCore/Security/*`)

* `OracleComp spec α`: query trees (a free monad) over an `OracleSpec`, with a
  dependent response type. `QueryBound w A n` is an explicit weighted query
  budget on every path. `simulate` runs a tree against a stateful oracle.
* `Prob`: `allTapes n R` enumerates all `R^n` tapes. `count` is a
  classically decided count, so games may use undecidable events such as
  "claim in language". `PrLE` is a probability bound as a `Nat` inequality.
  `PrLE.sure_iff` checks that the encoding is not vacuous.
* `Adversary`: `CoinAdversary` (randomized algorithm = coin-oracle program),
  `map` post-composition.
* `CR`: `CRReduction`, `BadAccept`, `Sound`, `CRSecure`, `secure_of_sound`.
* `ROM`: `LazyRO`, `romSpec`, `romImpl`, `romWins`, `RomSound`.
  `ROMLemmas` contains the invariant, the counting lemmas and
  `rom_guess_bound`.

## 7. How the judge checks a certificate

The recommended procedure, which the formal-checker lane implements:

1. Generate `Judge/Expected.lean` from the frozen challenge and the judge's
   own build outputs:
   ```lean
   import ArenaCore            -- pinned formal-core commit
   import NearSpec             -- pinned spec commit
   def Judge.params : ArenaCore.ChallengeParams := { spec := …, profile := …, verifyFuel := …, … }
   def Judge.artifacts : ArenaCore.ArtifactDescription :=
     { publicDigest := [0x57, …], impl := .interp [0xe7, …] }
   def Judge.Expected : Prop := ArenaCore.AdmissionStatement Judge.params Judge.artifacts
   ```
   `formal-core/Toy/Artifacts.lean` is a worked instance of this file.
2. Elaborate the candidate project against the **pinned** formal-core and
   spec. Refuse candidate modules in the `ArenaCore.*`, `NearSpec.*` or
   `Judge.*` namespaces, and refuse a candidate-provided `ArenaCore` package
   (`negative/10_tampered_core.lean`).
3. Elaborate a judge-written wrapper: `theorem Judge.check : Judge.Expected :=
   Candidate.certificate`. The kernel checks this, so a shadowed or different
   statement fails (`negative/06`, `07`, `08`, `11`). Leaning on the kernel's
   definitional equality is sound here because the expected type is
   judge-built.
4. Audit `#print axioms Judge.check` against the allowlist
   `[propext, Classical.choice, Quot.sound]`. This catches `sorryAx`, every
   candidate `axiom`, and `native_decide`, which in v4.34 shows up as the
   auxiliary axioms `<decl>._native.native_decide.ax_*`; older versions show
   `Lean.ofReduceBool`.
5. Export and re-check with independent kernels (`lean4checker`,
   `nanoda_lib`). `leanprover/comparator` implements steps 3–5 for exactly
   this "trusted challenge statement vs. untrusted solution" pattern.

`formal-core/negative/check_negative.sh` is a reference harness for steps 3–4.
It passes the positive control and rejects all 11 negative certificates.

## 8. Mapping to `common/arena-types` (proposed additive changes)

formal-core does not own `common/`. These fields are needed and should be
added by the owning lane (see `docs/CHANGELOG-contracts.md`):

* `ResourceLimits.verify_fuel` (→ `ChallengeParams.verifyFuel`) and
  `max_proof_bytes` (→ `maxProofBytes`), if not already present.
* `SecurityProfile.max_reduction_fuel` (→ `maxReductionFuel`).
* Candidate manifest: `[entry] verify_route = "npai-v1"`,
  `verifier_bytecode = "out/verifier.npai"`. For this route, `prepare` emits
  exactly `public_dir/public.bin` and the statement pins `sha256(public.bin)`.
* `Assumption.lean_decl` values:
  `ArenaCore.Assumptions.Sha256CollisionResistant`,
  `ArenaCore.Security.RomSound`.
* `FORMAL_IMPL_CONNECTION`'s evidence edge status comes from
  `VerifierImpl.status` (`checked` for `interp`, `trusted` for
  `nativeTrusted`).

## 9. Worked example: `Toy` (not NEAR)

`Toy/Spec.lean` defines a 4-byte table relation: claim `[i, v]` is true iff
`toyTable[i] = v`. The verifier sees only `pub = sha256 toyTable`, and the
proof is a table `T'`. It accepts iff `sha256 T' = pub` and `T'[i] = v`. In
`Toy/Certificate.lean`, `Toy.certificate : ToyJudge.Expected` proves the
**entire** admission statement:

* route (a): an 18-instruction verifier bytecode, whose digest is checked by
  the kernel and whose behaviour is characterised by symbolic execution of
  `Interp.exec` (`verifier_accepts`);
* completeness by kernel evaluation of the interpreter on all four true claims
  (`verifier_complete`);
* crypto soundness by the standard-model route. A 7-instruction reduction
  bytecode outputs `(proof, toyTable)` (`reduction_runOut`), which on any bad
  acceptance is a SHA-256 collision (`toyReduction_sound`).
* Non-triviality: there is a true and a false claim (`toy_nontrivial`).

## 10. Build and axioms (recorded 2026-10-03, Lean v4.34.1)

`cd formal-core && lake build` builds the default targets from clean in
**3.9 s wall time** (32 cores, 0.6 GB peak RSS): the core, the tests (pinned
NPAI vectors and SHA-256 vectors, one of them kernel-checked) and the Toy
certificate. `lake build arena-interp-ref` adds 1.1 s.

| theorem | axioms |
|---------|--------|
| `Toy.certificate` | propext, Classical.choice, Quot.sound |
| `ArenaCore.AdmissionStatement.endToEnd` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Obligations.endToEnd` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Security.CRReduction.secure_of_sound` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Security.rom_guess_bound` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Security.romSound_of_deterministic` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Sanity.acceptAll_not_romSound` | propext, Classical.choice, Quot.sound |
| `ArenaCore.Sanity.rejectAll_not_complete` | none |
| `ArenaCore.interpOracleVerifier_deployed` | propext, Quot.sound |
| `ArenaCore.sha256_length` | propext |
| `Toy.verifier_accepts` / `Toy.toyReduction_sound` | propext, Classical.choice, Quot.sound |
| `Toy.verifier_complete` | propext |

`Classical.choice` comes from counting with classically decided events.

## 11. Limitations

* **Interpreter TCB.** The Rust NPAI interpreter is trusted to implement
  `ArenaCore.Interp`. The evidence for this is differential testing (45 pinned
  vectors plus fuzzing against `arena-interp-ref`), not proof. The Lean
  reference is slow on large inputs because memory is a closure chain.
* **Kernel cost of digests.** Kernel SHA-256 costs about 0.15 s per 64-byte
  block. Digest bindings for multi-megabyte public parameters (e.g. SNARK
  keys) or very large bytecode would take minutes. A Merkle-chunked digest
  scheme would fix this, but none is implemented.
* **Keyless CR is relative.** The standard-model bound is relative to the
  collision advantage of an explicit finder whose cost is `cost(A) +
  maxReductionFuel`. The adversary's own cost is not formalised (adversaries
  are Lean functions). Tightness is 1, and the reduction's overhead is
  formal (fuel).
* **ROM.** The ROM is a heuristic. Only one ROM bound is proved here (preimage
  guessing), and there is no worked FS backend with a full `RomSound`
  certificate. The honest prover `P` in the game is the candidate's *model*.
  `ProverComplete` ties it to the verifier but not to the deployed prover
  binary. That is acceptable for validity-only profiles, because the prover's
  outputs are public anyway, but it would not suffice for zero-knowledge.
  Completeness is perfect (∀ hash functions). Statistically complete
  protocols would need a weaker, probabilistic completeness obligation.
* **Not modelled.** Zero knowledge (`FORMAL_ZK`), trusted-setup ceremonies
  (`approved_ceremony`: there is no setup game), post-quantum adversaries,
  aggregation depth, number of deployed proofs (`deployment_proofs_log2`),
  and assumptions beyond SHA-256 (discrete log, pairings, …). New assumptions
  are added as new `Prop`s in `ArenaCore.Assumptions` plus a `CryptoSound`
  branch. That is a governed change.
* **Two SHA-256 definitions.** `spec/lean` has its own `NearSpec.sha256`. If
  `NearRelation` uses it for state roots, collisions in it are not literally
  `ArenaCore.sha256` collisions. Either the spec lane imports
  `ArenaCore.SHA256`, or one proves the two equal. Both are FIPS 180-4
  implementations, so the proof is routine but has not been done.
* **Decoder canonicity** (`encode ∘ decode = id`) is tested, not proved. It
  is not needed for soundness: statements are about the image bytes.
* **Native route.** Route (b) is a trust edge by design. Nothing in Lean
  connects the binary to the model.
