import ZkFormal.Near.Extract.NodeViewLists

/-!
# ZkFormal.Near.Extract.NodeMain — the node table's traffic is its view's traffic
-/

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL

theorem stateZero {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 0) {x : Nat} (hx : x ∈ states) :
    tr.cell T_NODE r x = 0 := by
  have h := (rowFacts hL hr).2.1
  rw [ha] at h
  have b1 := cvb hL hr (x := sTAG) (by simp [boolCols, states])
  have b2 := cvb hL hr (x := sHPL) (by simp [boolCols, states])
  have b3 := cvb hL hr (x := sHPF) (by simp [boolCols, states])
  have b4 := cvb hL hr (x := sKEY) (by simp [boolCols, states])
  have b5 := cvb hL hr (x := sVLEN) (by simp [boolCols, states])
  have b6 := cvb hL hr (x := sVH) (by simp [boolCols, states])
  have b7 := cvb hL hr (x := sBM) (by simp [boolCols, states])
  have b8 := cvb hL hr (x := sCH) (by simp [boolCols, states])
  have b9 := cvb hL hr (x := sMEM) (by simp [boolCols, states])
  rw [cell_eq_cast tr T_NODE r sTAG, cell_eq_cast tr T_NODE r sHPL, cell_eq_cast tr T_NODE r sHPF,
    cell_eq_cast tr T_NODE r sKEY, cell_eq_cast tr T_NODE r sVLEN, cell_eq_cast tr T_NODE r sVH,
    cell_eq_cast tr T_NODE r sBM, cell_eq_cast tr T_NODE r sCH, cell_eq_cast tr T_NODE r sMEM] at h
  have S : cv tr T_NODE r sTAG + (cv tr T_NODE r sHPL + (cv tr T_NODE r sHPF + (cv tr T_NODE r sKEY +
      (cv tr T_NODE r sVLEN + (cv tr T_NODE r sVH + (cv tr T_NODE r sBM + (cv tr T_NODE r sCH +
      (cv tr T_NODE r sMEM + 0)))))))) = 0 := by
    apply fp_cast_eq (b := 0) (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add]
    have z0 : ((0 : Nat) : Fp) = 0 := rfl
    simp only [z0] at h ⊢; exact h
  apply of_cv_zero
  simp only [states, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- Inactive rows (other than row 0) emit nothing. -/
theorem padRowT {r : Nat} (hr : r < tr.height T_NODE) (ha : tr.cell T_NODE r act = 0) (hr0 : r ≠ 0)
    (bb : Nat) (sd : Bool) : rowT tr pub r bb sd = [] := by
  have z := fun x (hx : x ∈ states) => stateZero hL hr ha hx
  have hnf : tr.cell T_NODE r nf = 0 := bool01 hL hr (by simp [boolCols]) (fun h => by
    have := ((rowFacts hL hr).2.2.2.1 h).1; rw [ha] at this; exact fp_zero_ne_one this)
  have G := linkGates hL hr
  simp only at G
  have M := winMisc hL hr
  have hgP : tr.cell T_NODE r gP = 0 := by rw [G.1, z sCH (by simp [states])]; grind
  have hgD : tr.cell T_NODE r gD = 0 := by rw [M.2.1, hgP, z sVH (by simp [states])]; grind
  have hgV : tr.cell T_NODE r gV = 0 := by rw [G.2.1, hnf]; grind
  obtain ⟨GA, GB⟩ := gatesAt hL hr
  have hgA : tr.cell T_NODE r gA = 0 := by
    rw [GA, z sKEY (by simp [states]), z sHPF (by simp [states]), z sCH (by simp [states]), z sVH (by simp [states]),
      if_neg hr0]; grind
  have hgB : tr.cell T_NODE r gB = 0 := by rw [GB, z sKEY (by simp [states])]; grind
  by_cases b0 : bb = B_BYTES
  · subst b0; cases sd
    · exact rowT_bytesR r
    · rw [rowT_bytes, ha]; simp [gate]
  by_cases b1 : bb = B_DIGEST
  · subst b1; cases sd
    · rw [rowT_digest, hgD, if_neg hr0]; simp [gate]
    · exact rowT_digestS r
  by_cases b2 : bb = B_PARENT
  · subst b2; cases sd
    · rw [rowT_parentR, hnf, if_neg hr0, show (0 : Fp) - 0 = 0 by decide]; simp [gate]
    · rw [rowT_parentS, hgP]; simp [gate]
  by_cases b3 : bb = B_VSLOT
  · subst b3; cases sd
    · rw [rowT_vslotR, hgV]; simp [gate]
    · exact rowT_vslotS r
  by_cases b4 : bb = B_EDGE
  · subst b4; cases sd
    · rw [rowT_edgeR, hgA, hgB]; simp [gate]
    · rw [rowT_edgeS, hgA, hgB]; simp [gate]
  exact rowT_other r bb sd ⟨b0, b1, b2, b3, b4⟩

end ZkFormal.Near.NodeProof

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node ZkFormal.Near

def viewOf (tr : Trace Fp) (pub : List Fp) (segs : List (Nat × Nat)) : List NodeS :=
  segs.map fun p => nodeSOf tr pub p.1 p.2

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Node.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem NodeSegs.start0 (hS : NodeSegs tr segs) {q : Nat} (hq : q < segs.length) : segs[q].1 = 0 ↔ q = 0 := by
  obtain ⟨h0, f0⟩ := hS.first hL
  constructor
  · intro h
    rcases q with _ | k
    · rfl
    · exfalso
      have := hS.next hL (n := k) hq
      have hp := (hS.seg' hL (n := k) (by omega)).1
      omega
  · intro h; subst h; exact f0

theorem NodeSegs.endPos (hS : NodeSegs tr segs) : 1 ≤ segEnd 0 segs := by
  obtain ⟨h0, f0⟩ := hS.first hL
  have := hS.bound hL (List.getElem_mem h0); have := (hS.seg' hL h0).1; omega

theorem NodeSegs.lenLt (hS : NodeSegs tr segs) : segs.length ≤ tr.height T_NODE := by
  have hb : ∀ q (hq : q < segs.length), q < segs[q].1 + segs[q].2 := by
    intro q; induction q with
    | zero => intro hq; have := (hS.seg' hL hq).1; omega
    | succ q ih => intro hq; have := hS.next hL hq; have := ih (by omega); have := (hS.seg' hL hq).1; omega
  rcases Nat.eq_zero_or_pos segs.length with h | h
  · omega
  · have := hb (segs.length - 1) (by omega); have := hS.bound' hL (n := segs.length - 1) (by omega); omega

theorem rowsEq (hS : NodeSegs tr segs) (bb : Nat) (sd : Bool) :
    (List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb sd) =
      (List.range segs.length).flatMap fun q =>
        (List.range' (segs.getD q default).1 (segs.getD q default).2).flatMap fun r => rowT tr pub r bb sd := by
  rw [flatMap_rows_segs _ segs _ hS.consec hS.endLe (fun r h1 h2 => padRowT hL h2
    (zero_of hL h2 (by simp [boolCols]) (hS.pad r h1 h2)) (by have := hS.endPos hL; omega) bb sd)]
  exact flatMap_eq_range segs _

theorem nodePerm (hS : NodeSegs tr segs) (bb : Nat) :
    ((List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb true)).Perm
      ((nodeSends (viewOf tr pub segs) bb).map Msg.toFp) ∧
    ((List.range (tr.height T_NODE)).flatMap (fun r => rowT tr pub r bb false)).Perm
      ((nodeRecvs (viewOf tr pub segs) pub bb).map Msg.toFp) := by
  have hlen : (viewOf tr pub segs).length = segs.length := by simp [viewOf]
  have hne : viewOf tr pub segs ≠ [] := by
    obtain ⟨h0, -⟩ := hS.first hL
    exact List.ne_nil_of_length_pos (by rw [hlen]; exact h0)
  have hget : ∀ q (hq : q < segs.length), (viewOf tr pub segs).getD q default = nodeSOf tr pub segs[q].1 segs[q].2 := by
    intro q hq; rw [getD_eq_getElem' _ _ (by rw [hlen]; exact hq)]; simp [viewOf]
  have hH := hS.lenLt hL
  have hHP : tr.height T_NODE < P := by have := height_le hL; unfold P; omega
  have per : ∀ q (hq : q < segs.length),
      ((List.range' segs[q].1 segs[q].2).flatMap (fun r => rowT tr pub r bb true)).Perm
        ((pnSend q (nodeSOf tr pub segs[q].1 segs[q].2) bb).map Msg.toFp) ∧
      ((List.range' segs[q].1 segs[q].2).flatMap (fun r => rowT tr pub r bb false)).Perm
        ((pnRecv pub q (nodeSOf tr pub segs[q].1 segs[q].2) bb).map Msg.toFp) := fun q hq => by
    obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem hq)
    exact nodeAll hL hC (hS.nid hL q hq) (by omega) (hS.start0 hL hq) (hS.posAt hL hq) bb
  rw [rowsEq hL hS, rowsEq hL hS, sends_eq, recvs_eq _ _ _ hne, hlen, List.map_flatMap, List.map_flatMap]
  constructor
  · apply perm_flatMap_congr'; intro q hq; rw [List.mem_range] at hq
    rw [getD_eq_getElem' _ _ hq, hget q hq]; exact (per q hq).1
  · apply perm_flatMap_congr'; intro q hq; rw [List.mem_range] at hq
    rw [getD_eq_getElem' _ _ hq, hget q hq]; exact (per q hq).2

theorem nodeTrafficOf (hS : NodeSegs tr segs) :
    TableTraffic Node.interactions tr T_NODE pub (nodeTraffic (viewOf tr pub segs) pub) := by
  intro bb m
  rw [tableBusCount_eq, tableBusCount_eq]
  exact ⟨(nodePerm hL hS bb).1.count_eq m, (nodePerm hL hS bb).2.count_eq m⟩

end ZkFormal.Near.NodeProof
