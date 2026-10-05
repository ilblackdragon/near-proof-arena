import ZkFormal.Near.Compose
import ZkFormal.Near.Extract.Compose
import ZkFormal.Near.Spec.Sound
import ZkFormal.Near.Spec.Complete
import ZkFormal.Near.Extract.ShaFacts
import ZkFormal.Near.Extract.SortProof
import ZkFormal.Near.Extract.WalkProof
import ZkFormal.Near.Extract.AcctProof
import ZkFormal.Near.Extract.MrkProof

/-!
# ZkFormal.Near.Main — lane L6 top theorems with the proved parts plugged in

Remaining hypotheses: the six table-view extractions, the SHA contract
(`ShaFactsStmt`), linking (`LinkStmt`), and `RenderStmt` (honest trace).
`GoodSoundStmt` and `GoodCompleteStmt` are proved.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

theorem nearAir_sound' (hN : NodeViewStmt) (hW : WalkViewStmt) (hR : RcptViewStmt)
    (hA : AcctViewStmt) (hM : MrkViewStmt) (hS : SortViewStmt) (hSha : ShaFactsStmt)
    (hL : LinkStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound (extract_of_views hN hW hR hA hM hS hSha hL) good_sound

theorem nearAir_complete' (hR : RenderStmt) :
    ∀ (c : WfClaim) (w : Witness), NearRelation c.1 w → Holds nearAir (publicOf c) (honestTrace c w) :=
  nearAir_complete good_complete hR

theorem honestTrace_fits' (hR : RenderStmt) {c : WfClaim} {w : Witness} (h : NearRelation c.1 w) :
    ∀ t (ht : t < nearAir.tables.length),
      1 ≤ (honestTrace c w).log t ∧ (honestTrace c w).log t ≤ nearAir.tables[t].maxLog :=
  honestTrace_fits good_complete hR h

/-- Soundness with the SHA contract from lane L5 (proved). -/
theorem nearAir_sound_L5 (hN : NodeViewStmt) (hR : RcptViewStmt) (hL : LinkStmt) :
    ∀ (c : WfClaim) (tr : Trace Fp), Holds nearAir (publicOf c) tr → ∃ w, NearRelation c.1 w :=
  nearAir_sound' hN walk_view hR acct_view mrk_view sort_view shaFacts hL

end ZkFormal.Near
