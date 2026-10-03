import Candidate.Spec

/-!
# Backend predicate

For a zkVM the natural backend object would be "an accepting SP1 execution
trace of the pinned guest ELF on some input, whose public values are the claim
bytes". We have no Lean model of SP1's AIRs, of RISC-V execution of our ELF,
or of the Rust guest, so we cannot state that `B` faithfully.

We therefore choose the *weakest honest* backend: `Aux` is the relation's own
witness and `B c w := Rel c w`. Semantic soundness and completeness are then
trivial — and say nothing about SP1. **All of the zkVM-specific content is
moved into the cryptographic / implementation obligations**, which are open
(`Candidate.Pipeline`). We record this explicitly so nobody reads the two
proved theorems below as evidence about the zkVM.
-/

namespace Candidate

def backend : ArenaCore.Backend nearSpec where
  Aux := nearSpec.Witness
  B := nearSpec.Rel

/-- FORMAL_SEMANTIC_SOUNDNESS at the `B` level (vacuous for this choice of `B`). -/
theorem backend_semSound : backend.SemSound := fun _ w h => ⟨w, h⟩

/-- FORMAL_SEMANTIC_COMPLETENESS at the `B` level (vacuous for this choice of `B`). -/
theorem backend_semComplete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

end Candidate
