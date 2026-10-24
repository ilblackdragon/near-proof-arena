/-
Axiom audit for the D1 output-emission layer (`docs/evidence/lean-chunk-final-outputs/d1-outputs.md`).

Run from `spec/lean/v3`:

  lake env lean ../../../docs/evidence/lean-chunk-final-outputs/D1Axioms.lean

Every theorem printed below must report only `propext`, `Classical.choice`, `Quot.sound` — or no axioms.
`sorryAx` or any other axiom is a failure. The expected outputs are also listed in the evidence document.
-/
import NearSpecV3.ChunkValidationD1Out

#print axioms NearSpecV3.checkD1CoreObs_agrees
#print axioms NearSpecV3.checkD1CoreObs_reject
#print axioms NearSpecV3.checkD1CoreOut_agrees
#print axioms NearSpecV3.checkD1CoreOut_reject
#print axioms NearSpecV3.checkD1_accepted_observable_computed
#print axioms NearSpecV3.checkD1_ok_iff_coreOut_ok
#print axioms NearSpecV3.checkD1_error_iff_coreOut_error
#print axioms NearSpecV3.d1Outputs_fields
#print axioms NearSpecV3.d1Outputs_not_computed
#print axioms NearSpecV3.agreesWithHeaderD1_refl
