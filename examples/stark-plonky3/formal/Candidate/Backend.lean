import Candidate.Spec

/-!
# Backend predicate

The natural backend object is "a set of nine traces satisfying every AIR
constraint and balancing every LogUp bus, with public values = the claim's
fixed-width bytes". We have no Lean model of the AIRs (they live in Rust,
`source/src/air/`), so we cannot state that `B` faithfully yet.

We therefore use the weakest honest backend, `B c w := Rel c w`: semantic
soundness / completeness are then trivial and say **nothing** about the
STARK. All STARK-specific content is carried by the explicit hypotheses of
`Candidate.Pipeline` (AIR faithfulness, STARK/FRI/FS soundness, verifier
binding), which are open.
-/

namespace Candidate

def backend : ArenaCore.Backend nearSpec where
  Aux := nearSpec.Witness
  B := nearSpec.Rel

/-- FORMAL_SEMANTIC_SOUNDNESS at the `B` level (vacuous for this `B`). -/
theorem backend_semSound : backend.SemSound := fun _ w h => ⟨w, h⟩

/-- FORMAL_SEMANTIC_COMPLETENESS at the `B` level (vacuous for this `B`). -/
theorem backend_semComplete : backend.SemComplete := fun _ w _ h => ⟨w, h⟩

end Candidate
