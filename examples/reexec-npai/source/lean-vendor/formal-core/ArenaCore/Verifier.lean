import ArenaCore.Backend
import ArenaCore.Interp

/-!
# ArenaCore.Verifier — the production verifier model

The production verifier is modelled as a **total** Boolean function

  `verify : PublicArtifacts → ClaimBytes → ProofBytes → Bool`

(`Verifier`).  Totality and determinism are part of the model: the arena
calls `verify` on hostile inputs and treats anything but exit code 0 as
rejection, which corresponds to `false` here.

Because Fiat–Shamir-style verifiers hash, and the random-oracle game must
replace *the same* hash calls that the deployed verifier makes, every
verifier model is given *hash-parametrically* as an `OracleVerifier`: a
function of an arbitrary (stateful) hash oracle.  The deployed verifier is
that function instantiated with the deployed protocol hash
`Interp.deployedRO` = domain-separated SHA-256 (`OracleVerifier.deployed`).
For the approved-interpreter route the oracle verifier is *derived* from the
bytecode by `interpOracleVerifier`, so there is nothing for the candidate to
choose: the deployed function and the ROM function are the same bytecode run
under two hash oracles.

Two different properties are stated about a verifier and must not be
conflated:

* `DeterministicSound` — every accepted claim is in the language, for every
  input (no probability, no assumption).  This is "relation correctness".
* cryptographic soundness (`ArenaCore.Security`) — acceptance of a claim not
  in the language is *unlikely* for resource-bounded adversaries, under an
  approved assumption or idealised model.
-/

namespace ArenaCore

/-- Deployed verifier: `pub → claim → proof → accept?`. -/
abbrev Verifier := Bytes → Bytes → Bytes → Bool

/-- A verifier given parametrically in the hash oracle it uses. -/
structure OracleVerifier where
  run : {σ : Type} → Interp.HashOracle σ → σ → Bytes → Bytes → Bytes → Bool × σ

/-- The deployed verifier: the oracle verifier run with the deployed protocol
hash (domain-separated SHA-256). -/
def OracleVerifier.deployed (v : OracleVerifier) : Verifier :=
  fun pub cb pb => (v.run Interp.deployedRO () pub cb pb).1

/-- An honest prover given parametrically in its hash oracle (used for the
honest-proof oracle of the ROM game). -/
structure OracleProver (S : ChallengeSpec) where
  run : {σ : Type} → Interp.HashOracle σ → σ → Bytes → S.Claim → S.Witness → Bytes × σ

/-- The approved-interpreter verifier derived from a bytecode image. -/
def interpOracleVerifier (code : Bytes) (fuel : Nat) : OracleVerifier where
  run := fun H hs pub cb pb =>
    match Interp.decode code with
    | some p =>
      let r := Interp.runWith H hs p { pub, claim := cb, proof := pb } fuel
      (r.1 == .accept, r.2.hs)
    | none => (false, hs)

/-- The deployed function of the interpreter route is exactly the arena
interpreter's accept predicate on that bytecode. -/
theorem interpOracleVerifier_deployed (code : Bytes) (fuel : Nat) :
    (interpOracleVerifier code fuel).deployed = Interp.interpVerify code fuel := by
  funext pub cb pb
  simp only [OracleVerifier.deployed, interpOracleVerifier, Interp.interpVerify, Interp.run,
    Interp.runFull]
  cases Interp.decode code with
  | none => rfl
  | some p =>
    simp only
    cases (Interp.runWith Interp.deployedRO () p { pub, claim := cb, proof := pb } fuel).1 <;> rfl

variable (S : ChallengeSpec)

/-- Deterministic relation correctness w.r.t. a language `L`: every accepted
claim is in `L`.  No probability, no assumption. -/
def DeterministicSound (L : Bytes → Prop) (v : Verifier) (pub : Bytes) : Prop :=
  ∀ cb pb, v pub cb pb = true → L cb

/-- Verifier-level completeness: every in-domain true claim has a proof of
bounded size that the *deployed* verifier accepts on the canonical claim
encoding.  This is what rules out the always-rejecting verifier. -/
def VerifierComplete (v : Verifier) (pub : Bytes) (maxProofBytes : Nat) : Prop :=
  ∀ c w, S.Domain c → S.Rel c w →
    ∃ pb : Bytes, pb.length ≤ maxProofBytes ∧ v pub (S.encodeClaim c) pb = true

/-- Prover completeness for the ROM game: for *every* hash function, the
honest prover's proof of an in-domain true claim is accepted by the verifier
using the same hash function, and has bounded size. -/
def ProverComplete (v : OracleVerifier) (P : OracleProver S) (pub : Bytes)
    (maxProofBytes : Nat) : Prop :=
  ∀ (H : Bytes → Bytes) c w, S.Domain c → S.Rel c w →
    let pureH : Interp.HashOracle Unit := fun u m => (H m, u)
    let pb := (P.run pureH () pub c w).1
    pb.length ≤ maxProofBytes ∧ (v.run pureH () pub (S.encodeClaim c) pb).1 = true

end ArenaCore
