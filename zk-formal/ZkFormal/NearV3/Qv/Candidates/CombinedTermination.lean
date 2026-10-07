import ZkFormal.NearV3.Qv.Candidates.CombinedPlanMetadata
import ZkFormal.NearV3.Qv.Candidates.CombinedKeyEndpoints

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec

theorem plan_public_termination {F : Type} [Lean.Grind.CommRing F]
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast
      ((w.row pos b).getD c 0))
    (hpub : CombinedTable.kPublic.eval tr t r pub =
      @Nat.cast F Lean.Grind.Semiring.natCast pres.length) :
    (eqG (c CombinedTable.wend) (c ValueTable.tau) CombinedTable.kPublic).eval tr t r pub=0 := by
  change tr.cell t r CombinedTable.wend *
    (tr.cell t r ValueTable.tau + -CombinedTable.kPublic.eval tr t r pub)=0
  rw [hpub]
  cases hf : w.final
  · simp [hc,CombinedTable.wend,hf,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.zero_mul]
  · have ht := (plan_final_metadata pre v pres resolve w hw hf).1
    simp [hc,ValueTable.tau,ht,Lean.Grind.AddCommGroup.add_neg_cancel,Lean.Grind.Semiring.mul_zero]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
