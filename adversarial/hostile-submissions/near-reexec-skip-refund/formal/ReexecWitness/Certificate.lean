import ArenaExpectedInst
import ReexecWitness.Obligations
import ReexecWitness.PublicBin

/-!
# HOSTILE certificate

States the admission theorem for the attacker's restated, weakened challenge
(`weakParams`) instead of the judge's `ArenaExpectedInst.expectedType`. The
proof is genuine and axiom-clean, but it proves the wrong theorem. Writing it
at the judge's type is impossible, because the verifier accepts claims with any
refund outputs, which contradicts `DeterministicSound` for `NearRelation`.
-/

namespace ReexecWitness

open ArenaCore NearSpec.TransferV1

theorem certificate :
    AdmissionStatement
      (weakParams profileValidityClassical128 verifyFuelV1 maxProofBytesV1 maxReductionFuelV1)
      { publicDigest := ArenaExpected.publicDigest,
        impl := .nativeTrusted [] "leanprover/lean4:v4.34.1+leanc" Model.verifier } :=
  admission_weak _ _ _ _ (by decide) publicBin _ _ _ (by decide +kernel)

end ReexecWitness
