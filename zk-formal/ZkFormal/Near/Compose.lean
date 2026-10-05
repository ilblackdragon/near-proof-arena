import ZkFormal.Near.Statements

/-!
# ZkFormal.Near.Compose — lane L6 top theorems from the sublemma statements

DESIGN.md §9 L6:
* `nearAir_sound : ∀ c tr, Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w`
* `nearAir_complete : ∀ c w, NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w)`
* `honestTrace_fits : NearRelation c.1 w → ∀ t < #tables, log t ≤ maxLog t`
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

theorem nearAir_sound (hE : ExtractStmt) (hS : GoodSoundStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w := by
  intro c tr h
  obtain ⟨e, he⟩ := hE c tr h
  exact ⟨witnessOf e, hS c.1 e c.2 he⟩

theorem nearAir_complete (hC : GoodCompleteStmt) (hSm : SmallCompleteStmt) (hR : RenderStmt) :
    ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w) :=
  fun c w h => hR c (extOf c.1 w) (hC c.1 w h) (hSm c.1 w h)

theorem honestTrace_fits (hC : GoodCompleteStmt) (hSm : SmallCompleteStmt) (hR : RenderStmt) {c : WfClaim} {w : Witness}
    (h : NearRelation c.1 w) :
    ∀ t (ht : t < nearAir.tables.length),
      1 ≤ (honestTrace c w).log t ∧ (honestTrace c w).log t ≤ nearAir.tables[t].maxLog :=
  (nearAir_complete hC hSm hR c w h).logBound

end ZkFormal.Near
