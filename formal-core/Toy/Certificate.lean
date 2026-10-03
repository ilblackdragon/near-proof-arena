import Toy.BytecodeProofs
import Toy.Artifacts

/-!
# Toy: the candidate certificate

`Toy.certificate : ToyJudge.Expected` — a complete proof of the admission
statement for the toy challenge, via the approved-interpreter route and the
standard-model `sha256_cr` route for cryptographic soundness.
-/

namespace Toy

open ArenaCore Security Interp

/-- Backend semantics: `aux` is the table the claim was read from. -/
def toyBackend : Backend toySpec where
  Aux := Bytes
  B := fun c t => t = toyTable ∧ t[c.1.toNat]? = some c.2

theorem toyBackend_sound : toyBackend.SemSound := by
  rintro c t ⟨rfl, h⟩
  exact ⟨(), h⟩

theorem toyBackend_complete : toyBackend.SemComplete := by
  intro c w _ h
  exact ⟨toyTable, rfl, h⟩

/-- The explicit reduction: the shipped reduction bytecode with fuel 10000. -/
def toyReduction : CRReduction := ⟨reductionProg, 10000⟩

/-- The deployed verifier of the toy artifact. -/
abbrev toyVerifier : OracleVerifier := interpOracleVerifier verifierCode toyParams.verifyFuel

theorem toyVerifier_deployed :
    toyVerifier.deployed = interpVerify verifierCode 10000 :=
  interpOracleVerifier_deployed _ _

/-- Every bad acceptance is mapped by the reduction bytecode to an explicit
SHA-256 collision `(proof, toyTable)`. -/
theorem toyReduction_sound :
    toyReduction.Sound toyBackend.InLang toyVerifier.deployed toyPub := by
  rintro cb pb ⟨hacc, hnot⟩
  rw [toyVerifier_deployed] at hacc
  obtain ⟨hL, hsha, i, v, rfl, hpi⟩ := verifier_accepts cb pb hacc
  have hout : toyReduction.apply toyPub ([i, v], pb) = (pb, toyTable) := by
    simp only [CRReduction.apply, toyReduction]
    rw [reduction_runOut toyPub [i, v] pb hL (by rw [toyPub_length]; decide) (by simp [maxTapeLen])]
    rfl
  rw [hout]
  refine ⟨fun heq => ?_, hsha⟩
  simp only at heq
  subst heq
  exact hnot ⟨(i, v), rfl, toyTable, rfl, hpi⟩

/-- Completeness of the deployed verifier (honest proof = the table). -/
theorem toyVerifier_complete :
    VerifierComplete toySpec toyVerifier.deployed toyPub toyParams.maxProofBytes := by
  intro c w _ h
  refine ⟨toyTable, by decide, ?_⟩
  rw [toyVerifier_deployed]
  exact verifier_complete c h

theorem toyObligations : Obligations toyParams toyPub toyVerifier toyBackend where
  semSound := toyBackend_sound
  semComplete := toyBackend_complete
  verifierComplete := toyVerifier_complete
  cryptoSound := Or.inr
    ⟨List.mem_singleton.mpr rfl, toyReduction, Nat.le_refl _,
      CRReduction.secure_of_sound toyReduction_sound⟩

/-- **The toy certificate.** Its type is constructed by the judge. -/
theorem certificate : ToyJudge.Expected :=
  ⟨toyPub, toyVerifier, by decide +kernel,
    ⟨verifierCode, by decide +kernel, rfl⟩, toyBackend, toyObligations⟩

end Toy
