import ZkFormal.NearV3.Extract.Node.RowT

/-!
# ZkFormal.Near.Extract.NodeGlobal — the node segments of the table
-/

namespace ZkFormal.NearV3.NodeProof3
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.NodeV3 ZkFormal.Near

structure NodeSegs (tr : Trace Fp) (segs : List (Nat × Nat)) : Prop where
  consec : Consec 0 segs
  endLe : segEnd 0 segs ≤ tr.height T_NODE
  seg : ∀ p ∈ segs, IsSeg (one tr act) (one tr nf) (one tr nl) p.1 p.2
  pad : ∀ r, segEnd 0 segs ≤ r → r < tr.height T_NODE → one tr act r = false

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal NodeV3.table tr T_NODE pub)
include hL
variable {segs : List (Nat × Nat)}

theorem nodeSegs_exist : ∃ segs, NodeSegs tr segs := by
  have h2 := height_ge hL
  obtain ⟨segs, hc, hend, hall, hpad⟩ := segments_of (nodeSegFacts hL) (by omega)
  exact ⟨segs, hc, hend, hall, hpad⟩

theorem NodeSegs.bound (hS : NodeSegs tr segs) {p : Nat × Nat} (hp : p ∈ segs) :
    p.1 + p.2 ≤ segEnd 0 segs := (seg_le_end segs 0 hS.consec p hp).2

theorem NodeSegs.ctx (hS : NodeSegs tr segs) {p : Nat × Nat} (hp : p ∈ segs) :
    ∃ fl, NodeCtx tr p.1 p.2 fl := by
  have hb : p.1 + p.2 ≤ tr.height T_NODE := by have := hS.bound hL hp; have := hS.endLe; omega
  obtain ⟨fl, hF⟩ := fields_of hL (hS.seg p hp) hb
  exact ⟨fl, hS.seg p hp, hb, hF⟩

theorem NodeSegs.first (hS : NodeSegs tr segs) : ∃ h : 0 < segs.length, segs[0].1 = 0 := by
  have h2 := height_ge hL
  rcases Nat.eq_zero_or_pos segs.length with h | h
  · rw [List.length_eq_zero_iff] at h; subst h
    have := hS.pad 0 (by simp [segEnd]) (by omega)
    simp [one, (firstRow hL (by omega)).1] at this
  · refine ⟨h, ?_⟩
    have := hS.consec
    match segs, h with
    | p :: _, _ => exact this.1

theorem NodeSegs.next (hS : NodeSegs tr segs) {n : Nat} (h : n + 1 < segs.length) :
    segs[n + 1].1 = segs[n].1 + segs[n].2 := consec_get segs 0 hS.consec n h

theorem NodeSegs.seg' (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) :
    IsSeg (one tr act) (one tr nf) (one tr nl) segs[n].1 segs[n].2 := hS.seg _ (List.getElem_mem h)

theorem NodeSegs.bound' (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) :
    segs[n].1 + segs[n].2 ≤ tr.height T_NODE := by
  have := hS.bound hL (List.getElem_mem h); have := hS.endLe; omega

theorem NodeSegs.endEq (hS : NodeSegs tr segs) (h : 0 < segs.length) :
    segEnd 0 segs = segs[segs.length - 1].1 + segs[segs.length - 1].2 := segEnd_last segs 0 hS.consec h

/-- A node-constant column along node `n`. -/
theorem NodeSegs.const (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) {x : Nat} (hx : x ∈ nodeConst)
    {d : Nat} (hd : d < segs[n].2) : tr.cell T_NODE (segs[n].1 + d) x = tr.cell T_NODE segs[n].1 x := by
  obtain ⟨fl, hC⟩ := hS.ctx hL (List.getElem_mem h)
  exact segConst hL hC hx hd

/-- Node ids count the nodes. -/
theorem NodeSegs.nid (hS : NodeSegs tr segs) : ∀ n (h : n < segs.length),
    tr.cell T_NODE segs[n].1 nid = ((n : Nat) : Fp) := by
  intro n
  induction n with
  | zero =>
    intro h
    obtain ⟨_, h0⟩ := hS.first hL
    rw [h0]; exact (firstRow hL (by have := height_ge hL; omega)).2.2.1
  | succ n ih =>
    intro h
    have hs := hS.seg' hL (n := n) (by omega)
    have hb := hS.bound' hL (n := n + 1) h
    have hnx := hS.next hL h
    have hp := hs.1
    have hl := hs.2.2.1; rw [one_iff] at hl
    have ha : tr.cell T_NODE (segs[n].1 + segs[n].2 - 1 + 1) act = 1 := by
      have := (hS.seg' hL h).2.2.2.1 segs[n + 1].1 (by omega) (by have := (hS.seg' hL h).1; omega)
      rw [one_iff] at this; rwa [show segs[n].1 + segs[n].2 - 1 + 1 = segs[n + 1].1 by omega]
    have E := (atEnd hL (by have := (hS.seg' hL h).1; omega) hl).2 ha
    rw [show segs[n].1 + segs[n].2 - 1 + 1 = segs[n + 1].1 by omega] at E
    rw [E.2, show segs[n].1 + segs[n].2 - 1 = segs[n].1 + (segs[n].2 - 1) by omega,
      hS.const hL (by omega) (by simp [nodeConst]) (by omega), ih (by omega), natCast_add]
    rfl

/-- Positions count the rows of a node. -/
theorem NodeSegs.posAt (hS : NodeSegs tr segs) {n : Nat} (h : n < segs.length) :
    ∀ d, d < segs[n].2 → tr.cell T_NODE (segs[n].1 + d) pos = ((d : Nat) : Fp) := by
  have hs := hS.seg' hL h
  have hb := hS.bound' hL h
  have hp := hs.1
  have := counter_of (f := fun q => tr.cell T_NODE q Node.pos) (s := segs[n].1) (ℓ := segs[n].2) (v0 := 0)
    (by have := hs.2.1; rw [one_iff] at this
        show tr.cell T_NODE segs[n].1 Node.pos = _
        rw [((rowFacts hL (by omega)).2.2.2.1 this).2.2.2.1]; rfl)
    (fun q h1 h2 => by
      have ha := hs.2.2.2.1 q h1 (by omega); rw [one_iff] at ha
      have hl := zero_of hL (by omega) (by simp [boolCols]) (hs.2.2.2.2.2 q h1 h2)
      exact (inNode hL (by omega) ha hl).2.2.1)
  intro d hd
  have := this (segs[n].1 + d) (by omega) (by omega)
  simpa using this

end ZkFormal.NearV3.NodeProof3
