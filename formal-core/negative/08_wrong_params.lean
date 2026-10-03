-- EXPECT: THEOREM_TYPE_MISMATCH
-- Admission for a *different* challenge: the candidate weakened the profile
-- (allows `sha256_cr` but with a larger reduction-fuel cap) / changed fuel.
import Toy.Certificate
namespace Candidate
open ArenaCore
def myParams : ChallengeParams := { Toy.toyParams with maxReductionFuel := 1000000000 }
theorem certificate : AdmissionStatement myParams ToyJudge.artifacts :=
  ⟨Toy.toyPub, Toy.toyVerifier, by decide +kernel,
    ⟨Toy.verifierCode, by decide +kernel, rfl⟩, Toy.toyBackend,
    { semSound := Toy.toyBackend_sound, semComplete := Toy.toyBackend_complete,
      verifierComplete := Toy.toyVerifier_complete,
      cryptoSound := Or.inr ⟨List.mem_singleton.mpr rfl, Toy.toyReduction, by decide,
        Security.CRReduction.secure_of_sound Toy.toyReduction_sound⟩ }⟩
end Candidate
