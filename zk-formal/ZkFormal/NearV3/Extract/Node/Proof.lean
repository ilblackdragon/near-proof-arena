import ZkFormal.NearV3.Extract.Node.WfProof

/-!
# ZkFormal.Near.Extract.NodeProof — `node_view : NodeViewStmt`
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem szPrefix (hS : NodeSegs tr segs) : ∀ q (hq : q < segs.length),
    tr.cell T_NODE segs[q].1 sz = ((((segs.take q).map (szOf tr)).sum : Nat) : Fp) := by
  intro q
  induction q with
  | zero =>
    intro hq
    obtain ⟨_, f0⟩ := hS.first hL
    rw [f0]; simp; exact (firstRow hL (by have := height_ge hL; omega)).2.2.2.2
  | succ q ih =>
    intro hq
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show q < segs.length by omega))
    have hnx := hS.next hL hq
    have hb := hS.bound' hL hq
    have hp := (hS.seg' hL hq).1
    rw [hnx, szNode hL hC (by omega), ih (by omega), List.take_succ, List.map_append, List.sum_append,
      List.getElem?_eq_getElem (by omega)]
    simp [szOf, natCast_add]

theorem endFacts (hS : NodeSegs tr segs) :
    segEnd 0 segs < tr.height T_NODE ∧ tr.cell T_NODE (segEnd 0 segs) sumr = 1 ∧
    tr.cell T_NODE (segEnd 0 segs) sz = (((segs.map (szOf tr)).sum : Nat) : Fp) := by
  obtain ⟨h0, -⟩ := hS.first hL
  have hE := hS.endEq hL h0
  have hl := (hS.seg' hL (n := segs.length - 1) (by omega))
  have hb := hS.bound' hL (n := segs.length - 1) (by omega)
  have hpos := hl.1
  have hlt : segEnd 0 segs < tr.height T_NODE := by
    rcases Nat.lt_or_ge (segEnd 0 segs) (tr.height T_NODE) with h | h
    · exact h
    · exfalso
      have ha := hl.2.2.2.1 (tr.height T_NODE - 1) (by have := hl.1; omega) (by omega)
      rw [one_iff, lastRow hL (by omega)] at ha; exact fp_zero_ne_one ha
  have hnl := hl.2.2.1; rw [one_iff] at hnl
  have E := (atEnd hL (r := segEnd 0 segs - 1) (by have := hl.1; omega) (by
    rw [show segEnd 0 segs - 1 = segs[segs.length - 1].1 + segs[segs.length - 1].2 - 1 by omega]; exact hnl)).1
  rw [show segEnd 0 segs - 1 + 1 = segEnd 0 segs by have := hl.1; omega] at E
  have hpad := zero_of hL hlt (by simp [boolCols]) (hS.pad (segEnd 0 segs) (Nat.le_refl _) hlt)
  rw [hpad] at E
  refine ⟨hlt, by rw [← E]; grind, ?_⟩
  obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show segs.length - 1 < segs.length by omega))
  rw [hE, szNode hL hC (by omega), szPrefix hL hS _ (by omega)]
  have ht : ((segs.take (segs.length - 1 + 1)).map (szOf tr)).sum =
      ((segs.take (segs.length - 1)).map (szOf tr)).sum + szOf tr segs[segs.length - 1] := by
    rw [List.take_succ, List.getElem?_eq_getElem (by omega), List.map_append, List.sum_append]; simp
  rw [show segs.length - 1 + 1 = segs.length by omega, List.take_of_length_le (Nat.le_refl _)] at ht
  rw [ht]; simp only [natCast_add, szOf]

theorem sizeBound (hS : NodeSegs tr segs) : (segs.map (szOf tr)).sum ≤ 3000000 := by
  obtain ⟨hlt, hs, hz⟩ := endFacts hL hS
  obtain ⟨S1, S2⟩ := (sizeFacts hL hlt).2 hs
  rw [hz, eval_bits tr T_NODE _ pub reg 0 22 (fun b hb => S2 (0 + b) (by omega)), ← natCast_add] at S1
  have hbv := bitsVal_lt (fun b => cv tr T_NODE (segEnd 0 segs) (reg b)) 0 22
    (fun b hb => cv_bool (S2 (0 + b) (by omega)))
  have gen : ∀ (l : List (Nat × Nat)) (s0 : Nat), Consec s0 l →
      (∀ p ∈ l, IsSeg (one tr act) (one tr nf) (one tr nl) p.1 p.2 ∧ p.1 < tr.height T_NODE) →
      (l.map (szOf tr)).sum ≤ 73 * (segEnd s0 l - s0) := by
    intro l; induction l with
    | nil => intro s0 _ _; simp
    | cons p rest ih =>
      intro s0 hc hall
      obtain ⟨a, b'⟩ := p
      obtain ⟨rfl, hc'⟩ := hc
      have h1 := ih (a + b') hc' (fun q hq => hall q (by simp [hq]))
      have hp : 0 < b' := (hall (a, b') (by simp)).1.1
      have htv : cv tr T_NODE a tv ≤ 1 := cv_bool (isBool hL (hall (a, b') (by simp)).2 (x := tv) (by simp [boolCols]))
      have := segEnd_ge rest (a + b') hc'
      simp only [List.map_cons, List.sum_cons, segEnd, szOf]
      omega
  have hs73 := gen segs 0 hS.consec (fun p hp => ⟨hS.seg p hp, by
    have := hS.bound hL hp; have := hS.endLe; have := (hS.seg p hp).1; omega⟩)
  have hH := height_le hL
  have hEH := hS.endLe
  have N := fp_cast_eq (by unfold P; omega) (by unfold P; omega) S1
  omega

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem touchedNode {s ℓ : Nat} {fl : List (Nat × Nat)} (hC : NodeCtx tr s ℓ fl) :
    (nodeVOf tr s).touched = (cv tr T_NODE s tv == 1) := by
  obtain ⟨hr0, ha0⟩ := nodeStart hL hC
  have T := typeSumNat hL hr0 ha0
  have F := (flags hL hr0).2.2.1
  have hz : cv tr T_NODE s tv * (cv tr T_NODE s tb1 + cv tr T_NODE s te) = 0 := by
    rw [cell_eq_cast tr T_NODE s tv, cell_eq_cast tr T_NODE s tb1, cell_eq_cast tr T_NODE s te, ← natCast_add,
      ← natCast_mul] at F
    have b1 := cvb hL hr0 (x := tv) (by simp [boolCols])
    have b2 := cvb hL hr0 (x := tb1) (by simp [boolCols])
    have b3 := cvb hL hr0 (x := te) (by simp [boolCols])
    have := Nat.mul_le_mul b1 (show cv tr T_NODE s tb1 + cv tr T_NODE s te ≤ 2 by omega)
    exact fp_cast_eq (b := 0) (by unfold P; omega) (by unfold P; omega) (F.trans rfl)
  exact touched_iff tr s hz (by omega)

theorem nodeWfOf (hS : NodeSegs tr segs) : NodeWf (viewOf tr pub segs) := by
  have hlen : (viewOf tr pub segs).length = segs.length := by simp [viewOf]
  obtain ⟨h0, f0⟩ := hS.first hL
  have hget : ∀ n (hn : n < (viewOf tr pub segs).length),
      (viewOf tr pub segs)[n] = nodeSOf tr pub segs[n].1 segs[n].2 := by
    intro n hn; simp [viewOf]
  have hH := hS.lenLt hL
  have hHP : tr.height T_NODE < P := by have := height_le hL; unfold P; omega
  have mem : ∀ S ∈ viewOf tr pub segs, ∃ p ∈ segs, S = nodeSOf tr pub p.1 p.2 := by
    intro S hS'; simp only [viewOf, List.mem_map] at hS'; obtain ⟨p, hp, rfl⟩ := hS'; exact ⟨p, hp, rfl⟩
  refine ⟨List.ne_nil_of_length_pos (by rw [hlen]; exact h0), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    obtain ⟨fl, hC⟩ := hS.ctx hL hp
    exact (nodeV_wf hL hC).1
  · obtain ⟨q, rest, hq⟩ := List.exists_cons_of_length_pos h0
    have hq0 : q.1 = 0 := by subst hq; simpa using f0
    subst hq
    show cv tr T_NODE q.1 depth = 0
    rw [hq0]; unfold cv; rw [(firstRow hL (by have := height_ge hL; omega)).2.2.2.1]; exact Fp.toNat_zero
  · intro n hn
    rw [hget]
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show n < segs.length by omega))
    exact resOkNode hL hC (hS.nid hL n (by omega)) (by omega)
  · intro n hn
    rw [hget]
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem (show n < segs.length by omega))
    exact usesLen hL hC (hS.nid hL n (by omega)) (by omega) (hS.start0 hL (by omega))
  · have : (viewOf tr pub segs).map (fun S => (S.v.ser false).length + (if S.v.touched then 72 else 0)) =
        segs.map (szOf tr) := by
      unfold viewOf; rw [List.map_map]; apply List.map_congr_left; intro p hp
      obtain ⟨fl, hC⟩ := hS.ctx hL hp
      simp only [Function.comp, nodeSOf]
      rw [← (nodeSer hL hC).1, rowsB_length, szOf]
      simp only [touchedNode hL hC]
      have := cvb hL (r := p.1) (by have := hC.bound; have := hC.seg.1; omega) (x := tv) (by simp [boolCols])
      by_cases ht : cv tr T_NODE p.1 tv = 1 <;> simp [ht] <;> omega
    rw [this]; exact sizeBound hL hS
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    exact ⟨cv_lt _ _ _ _, cv_lt _ _ _ _, uses_lt tr pub p.1 p.2⟩
  · intro S hS'; obtain ⟨p, hp, rfl⟩ := mem S hS'
    obtain ⟨fl, hC⟩ := hS.ctx hL hp
    exact (nodeV_wf hL hC).2

end ZkFormal.NearV3.NodeProof3

namespace ZkFormal.Near

/-- **The node table extracts.** -/
theorem node_view : NodeViewStmt := by
  intro tr pub hL
  obtain ⟨segs, hS⟩ := NodeProof.nodeSegs_exist hL
  exact ⟨NodeProof.viewOf tr pub segs, NodeProof.nodeWfOf hL hS, NodeProof.nodeTrafficOf hL hS⟩

end ZkFormal.Near
