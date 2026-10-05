import ZkFormal.Near.Extract.NodeWfProof

/-!
# ZkFormal.Near.Extract.NodeProof — `node_view : NodeViewStmt`
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
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

end ZkFormal.Near.NodeProof
