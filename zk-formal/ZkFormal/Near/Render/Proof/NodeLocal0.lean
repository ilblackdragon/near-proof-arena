import ZkFormal.Near.Render.Proof.NodeTraffic1
import ZkFormal.Near.Render.Proof.NodeTraffic2
import ZkFormal.Near.Render.Proof.ShaFit2

/-!
# ZkFormal.Near.Render.Proof.NodeLocal0 — the node table's height

The honest node table has at most `3·10^6` node rows (`Good.size`), so its
log-height is at most `maxLog = 22`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace NodeLoc
open NodeCells NodeGen NodeInfo NodeTr

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hs : Small e)
include hg hs

theorem recs_len : (recsOf (mkInfo c.1 e)).length ≤ 3000000 := by
  simp only [recsOf, List.length_flatMap, info_N]
  have h1 : ((List.range e.ns.length).map fun n => (nodeRecs (mkInfo c.1 e) n).length) =
      (List.range e.ns.length).map fun n => ((mkInfo c.1 e).pre.getD n []).length := by
    apply List.map_congr_left; intro n hn
    rw [nodeRecs_len, (len_pre hg hs (List.mem_range.1 hn)).1]
  rw [h1]
  have h2 : ((List.range e.ns.length).map fun n => ((mkInfo c.1 e).pre.getD n []).length).sum ≤
      ((List.range e.ns.length).map fun n => nodeSize (e.ns.toArray.getD n (.branch none [] 0))).sum := by
    apply sum_map_le; intro n _
    have := (pre_ok c.1 e hg n).1
    simp only [Info.nodeAt, mkInfo_ns] at this
    unfold nodeSize; unfold sz0 at this; omega
  rw [range_map_getD e.ns _ nodeSize] at h2
  have := hg.size
  simp only [revealedOf, Params.maxWitnessBytes] at this
  omega

theorem node_log : 1 ≤ (render c.1 e).log T_NODE ∧ (render c.1 e).log T_NODE ≤ Node.maxLog := by
  obtain ⟨hl, _, _⟩ := node_render c.1 e
  rw [hl]
  refine ⟨one_le_logOf _, logOf_le (by decide) ?_⟩
  have := recs_len hg hs
  simp only [Node.maxLog]; omega

end

theorem gate_le (I : Info) (u : Std.HashMap Edge Nat) (recs : Array NRec) (total q col : Nat)
    (hcol : col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 143 ∨ col = 144 ∨ col = 145 ∨ col = 160) :
    cell I u recs total q col ≤ 1 := by
  simp only [cell]
  split
  · generalize recs.getD q default = r
    rcases hcol with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rc_act]; exact Nat.le_refl _
    · rw [rc_nf]; simp only [b2n]; split <;> omega
    · rw [rc_gD]; split <;> omega
    · rw [rc_gP]; split <;> omega
    · rw [rc_gV]; simp only [b2n]; split <;> omega
    · rw [rc_gA]; simp only [gateCell]; split <;> omega
    · rw [rc_gB]; simp only [gateCell]; split <;> omega
  · split <;> rcases hcol with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [sumCell, padCell, Node.sumr, Node.sz]

theorem ofNat01 {v : Nat} (h : v ≤ 1) : Fp.ofNat v = 0 ∨ Fp.ofNat v = 1 := by
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem node_bits : ∀ r, r < (render c.1 e).height T_NODE → ∀ i ∈ Node.interactions, ∀ b ∈ i.mult,
    b.eval (render c.1 e) T_NODE r (publicOf c) = 0 ∨ b.eval (render c.1 e) T_NODE r (publicOf c) = 1 := by
  obtain ⟨_, hH, hcell⟩ := node_render c.1 e
  intro q hq i hi b hb
  rw [hH] at hq
  have hc : ∀ col, (col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 143 ∨ col = 144 ∨ col = 145 ∨ col = 160) →
      (render c.1 e).cell T_NODE q col = 0 ∨ (render c.1 e).cell T_NODE q col = 1 := by
    intro col hcol
    rw [hcell q col hq (by rcases hcol with h | h | h | h | h | h | h <;> subst h <;> decide)]
    exact ofNat01 (gate_le _ _ _ _ q col hcol)
  simp only [Node.interactions, send, recv, List.mem_cons, List.not_mem_nil, or_false] at hi
  have hcol : ∀ col, (col = 0 ∨ col = 1 ∨ col = 142 ∨ col = 143 ∨ col = 144 ∨ col = 145 ∨ col = 160) →
      (Dsl.c col).eval (render c.1 e) T_NODE q (publicOf c) = 0 ∨ (Dsl.c col).eval (render c.1 e) T_NODE q (publicOf c) = 1 :=
    fun col h => by rw [eval_c]; exact hc col h
  have hfirst : Expr.isFirst.eval (render c.1 e) T_NODE q (publicOf c) = 0 ∨
      Expr.isFirst.eval (render c.1 e) T_NODE q (publicOf c) = 1 := by
    rw [eval_isFirst]; split <;> simp
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.mem_singleton] at hb <;> subst hb
  · exact hcol 0 (by simp)
  · exact hcol 0 (by simp)
  · exact hcol 142 (by simp)
  · exact hcol 142 (by simp)
  · exact hfirst
  · exact hfirst
  · exact hcol 143 (by simp)
  rotate_left
  · exact hcol 144 (by simp)
  · exact hcol 145 (by simp)
  · exact hcol 145 (by simp)
  · exact hcol 160 (by simp)
  · exact hcol 160 (by simp)
  -- the PARENT receive gate `nf − isFirst`
  simp only [eval_sub, eval_c, eval_isFirst, Node.nf]
  have hN0 : 0 < (mkInfo c.1 e).ns.size := by rw [info_N]; exact hg.shape.nonempty
  rw [hcell q 1 hq (by decide)]
  by_cases h0 : q = 0
  · subst h0
    have hR : 0 < (recsOf (mkInfo c.1 e)).length := by
      unfold recsOf
      obtain ⟨M, hM⟩ : ∃ M, (mkInfo c.1 e).ns.size = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN0).symm⟩
      rw [hM, List.range_succ_eq_map, List.flatMap_cons]
      have := layN_pos (mkInfo c.1 e) 0; rw [← nodeRecs_len] at this
      simp; omega
    have := (first_iff (mkInfo c.1 e) hN0 hR).1 rfl
    simp only [cell, recsA, List.size_toArray, hR, if_true, rc_nf]
    have h2 : ((recsOf (mkInfo c.1 e))[0]?.getD default).pos = 0 := by
      rw [← List.getD_eq_getElem?_getD]; exact this.2
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, b2n, h2]
    left; decide
  · simp only [h0, if_false]
    have := gate_le (mkInfo c.1 e) (edgeUses (walksOf (mkInfo c.1 e))) (recsA (mkInfo c.1 e)) (totalOf (mkInfo c.1 e))
      q 1 (by simp)
    rcases ofNat01 this with h | h <;> rw [h] <;> decide

end

end NodeLoc

end ZkFormal.Near.Render
