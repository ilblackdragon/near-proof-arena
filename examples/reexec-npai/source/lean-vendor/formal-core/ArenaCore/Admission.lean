import ArenaCore.Security.CR
import ArenaCore.Security.ROM

/-!
# ArenaCore.Admission — the judge-constructed theorem type

`AdmissionStatement ch art : Prop` is the *type* the judge constructs from

* `ch : ChallengeParams` — the frozen challenge (relation, domain, claim
  codec, security profile, resource limits), and
* `art : ArtifactDescription` — the exact certified artifacts, by digest
  (public-artifact digest, verifier bytecode digest or native binary digest).

A candidate's certificate is a term of this type.  The judge never reads
the candidate's statement of what it proved; it elaborates this definition
itself and checks the candidate's term against it.

```
AdmissionStatement ch art :=
  ∃ pub v,
    sha256 pub = art.publicDigest ∧                -- public artifacts pinned
    art.impl.Connection ch.verifyFuel v ∧          -- FORMAL_IMPL_CONNECTION
    ∃ bk : Backend ch.spec,
      bk.SemSound ∧                                -- FORMAL_SEMANTIC_SOUNDNESS
      bk.SemComplete ∧                             -- FORMAL_SEMANTIC_COMPLETENESS
      VerifierComplete ch.spec v.deployed pub ch.maxProofBytes ∧
      CryptoSound ch pub v bk                      -- FORMAL_CRYPTO_SOUNDNESS
```
-/

namespace ArenaCore

open Security

/-- Security model of a profile. -/
inductive SecModel where
  | standard
  | randomOracle
  deriving DecidableEq, Repr

/-- Lean mirror of the governed `SecurityProfile` (fields used in theorem
types). -/
structure SecurityProfile where
  id : String
  model : SecModel
  targetBits : Nat
  allowedAssumptions : List AssumptionId
  maxProverQueriesLog2 : Nat
  maxHashQueriesLog2 : Nat

/-- Everything the challenge fixes. -/
structure ChallengeParams where
  spec : ChallengeSpec
  profile : SecurityProfile
  /-- Fuel given to the approved interpreter for one `verify` call. -/
  verifyFuel : Nat
  /-- Maximum honest proof size (resource limit). -/
  maxProofBytes : Nat
  /-- Maximum fuel of an explicit security reduction program. -/
  maxReductionFuel : Nat

/-- How the executed verifier is connected to the formal model. -/
inductive VerifierImpl where
  /-- Approved interpreter: the arena runs the judge-owned interpreter on
  the bytecode image with this SHA-256 digest.  Status: **checked** (modulo
  the interpreter itself, which is in the TCB and differentially tested). -/
  | interp (bytecodeDigest : Digest)
  /-- Native binary built by a governed trusted toolchain from sources whose
  model is `model`.  Status: **trusted** — the binary ↔ model edge is a
  trusted-base entry, never reported as checked. -/
  | nativeTrusted (binaryDigest : Digest) (toolchainId : String) (model : OracleVerifier)

/-- Exact certified artifacts. -/
structure ArtifactDescription where
  /-- SHA-256 of the public-artifact tape (judge-run `prepare` output). -/
  publicDigest : Digest
  impl : VerifierImpl

/-- Evidence-graph status of the implementation-connection edge. -/
inductive EdgeStatus where
  | checked
  | trusted
  deriving DecidableEq, Repr

def VerifierImpl.status : VerifierImpl → EdgeStatus
  | .interp _ => .checked
  | .nativeTrusted _ _ _ => .trusted

/-- `FORMAL_IMPL_CONNECTION`: which oracle verifier the obligations are about.
For the interpreter route it is *derived* from bytecode with the pinned
digest; the candidate chooses nothing. -/
def VerifierImpl.Connection : VerifierImpl → Nat → OracleVerifier → Prop
  | .interp d, fuel, v => ∃ code : Bytes, sha256 code = d ∧ v = interpOracleVerifier code fuel
  | .nativeTrusted _ _ m, _, v => v = m

/-- `FORMAL_CRYPTO_SOUNDNESS`.  Either deterministic soundness (no
assumption), or the profile's model:

* standard model: an explicit fuel-bounded reduction to SHA-256 collisions,
  stated relative to the judge-supplied `sha256_cr` hypothesis
  (only if `sha256_cr` is allowed by the profile);
* random-oracle model: an honest prover that is complete for every hash
  function, and the ROM game bound at the profile's query budgets with
  `num/den ≤ 2^-targetBits` (checked by kernel `Nat` arithmetic). -/
def CryptoSound (ch : ChallengeParams) (pub : Bytes) (v : OracleVerifier)
    (bk : Backend ch.spec) : Prop :=
  DeterministicSound bk.InLang v.deployed pub ∨
  match ch.profile.model with
  | .standard =>
    AssumptionId.sha256CollisionResistance ∈ ch.profile.allowedAssumptions ∧
    ∃ r : CRReduction, r.fuel ≤ ch.maxReductionFuel ∧ CRSecure r bk.InLang v.deployed pub
  | .randomOracle =>
    AssumptionId.sha256RandomOracle ∈ ch.profile.allowedAssumptions ∧
    ∃ P : OracleProver ch.spec, ProverComplete ch.spec v P pub ch.maxProofBytes ∧
    ∃ tapeLen num den : Nat, num * 2 ^ ch.profile.targetBits ≤ den ∧
      RomSound ch.spec bk.InLang v P pub
        (2 ^ ch.profile.maxHashQueriesLog2) (2 ^ ch.profile.maxProverQueriesLog2)
        tapeLen num den

/-- The per-backend obligations (named fields = obligation ids). -/
structure Obligations (ch : ChallengeParams) (pub : Bytes) (v : OracleVerifier)
    (bk : Backend ch.spec) : Prop where
  semSound : bk.SemSound
  semComplete : bk.SemComplete
  verifierComplete : VerifierComplete ch.spec v.deployed pub ch.maxProofBytes
  cryptoSound : CryptoSound ch pub v bk

/-- **The expected theorem type.** -/
def AdmissionStatement (ch : ChallengeParams) (art : ArtifactDescription) : Prop :=
  ∃ (pub : Bytes) (v : OracleVerifier),
    sha256 pub = art.publicDigest ∧
    art.impl.Connection ch.verifyFuel v ∧
    ∃ bk : Backend ch.spec, Obligations ch pub v bk

/-! ## What admission buys: end-to-end statements about the relation -/

/-- End-to-end soundness at the level of the challenge relation (no
backend vocabulary): one of the three soundness forms, for `S.InLang`. -/
def EndToEndSound (ch : ChallengeParams) (pub : Bytes) (v : OracleVerifier) : Prop :=
  DeterministicSound ch.spec.InLang v.deployed pub ∨
  (∃ r : CRReduction, r.fuel ≤ ch.maxReductionFuel ∧
      CRSecure r ch.spec.InLang v.deployed pub) ∨
  (∃ P : OracleProver ch.spec, ∃ tapeLen num den : Nat,
      num * 2 ^ ch.profile.targetBits ≤ den ∧
      RomSound ch.spec ch.spec.InLang v P pub
        (2 ^ ch.profile.maxHashQueriesLog2) (2 ^ ch.profile.maxProverQueriesLog2) tapeLen num den)

theorem Obligations.endToEnd {ch : ChallengeParams} {pub : Bytes} {v : OracleVerifier}
    {bk : Backend ch.spec} (h : Obligations ch pub v bk) : EndToEndSound ch pub v := by
  have hL : ∀ cb, bk.InLang cb → ch.spec.InLang cb := fun _ => bk.inLang_rel h.semSound
  rcases h.cryptoSound with hdet | hc
  · exact Or.inl fun cb pb hacc => hL _ (hdet cb pb hacc)
  · revert hc
    cases ch.profile.model with
    | standard =>
      rintro ⟨_, r, hf, hs⟩
      exact Or.inr (Or.inl ⟨r, hf, hs.mono hL⟩)
    | randomOracle =>
      rintro ⟨_, P, _, n, num, den, hb, hs⟩
      exact Or.inr (Or.inr ⟨P, n, num, den, hb, hs.mono hL⟩)

/-- Admission implies: pinned public artifacts, connected verifier,
completeness of the deployed verifier, and end-to-end soundness for the
challenge relation. -/
theorem AdmissionStatement.endToEnd {ch : ChallengeParams} {art : ArtifactDescription}
    (h : AdmissionStatement ch art) :
    ∃ (pub : Bytes) (v : OracleVerifier),
      sha256 pub = art.publicDigest ∧ art.impl.Connection ch.verifyFuel v ∧
      VerifierComplete ch.spec v.deployed pub ch.maxProofBytes ∧ EndToEndSound ch pub v := by
  obtain ⟨pub, v, hpub, hconn, bk, hob⟩ := h
  exact ⟨pub, v, hpub, hconn, hob.verifierComplete, hob.endToEnd⟩

end ArenaCore
