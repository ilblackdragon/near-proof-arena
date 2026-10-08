import ZkFormal.NearV3.Render.Ups.CompactRowGroup
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

theorem compact_cWalk {insts : List UpsInst} (hpos : 0<insts.length)
    (hi : ∀I∈insts,InstOk I) {H : Nat} (hH : compactR insts+1≤H) :
    CompactGroupOk insts H UpsV3.cWalk := by
  apply compact_groupOk_by hpos hH (fun e he=>by simp [compactConstraints,he])
  · intro i hi' t ht q hq hr C D P hC hD ex hex
    have iok := hi _ (inst_mem hi')
    have hn : ∀ t', t' = t + 1 → t < 3 → ∀ x, x < 200 → D x = WC (inst insts i) t' x := by
      intro t' e h3 x hx
      rw [hD x hx, compact_nextRow hpos hi hq hr (rk' := .w t') (by simp only [compactNext]; rw [ite_eq_left (by omega), e]) x, compactRowCell_w]
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 by omega) with rfl | rfl | rfl | rfl
    · exact walk_w0 iok hC (hn 1 rfl (by decide)) ex hex
    · exact walk_w1 iok hC (hn 2 rfl (by decide)) ex hex
    · exact walk_w2 iok hC (hn 3 rfl (by decide)) ex hex
    · exact walk_w3 iok hC ex hex
  · intro i hi' k p hk hp q hq hr C D P hC hD ex hex
    exact vzC (zc:=zQ) (fun x hx=>by
      rw [hC x (by simp [zQ] at hx; omega)]
      exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx)
      (List.all_eq_true.1 (show UpsV3.cWalk.all (vz zQ (fun _=>false) false false false)=true by decide) ex hex)

end ZkFormal.NearV3.Render.UpsRelay
