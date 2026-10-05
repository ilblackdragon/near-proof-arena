import ZkFormal.Near.Extract.NodeFacts2

/-!
# ZkFormal.Near.Extract.NodeSegs — nodes and fields as row segments
-/

namespace ZkFormal.Near.NodeProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}

def one (tr : Trace Fp) (x r : Nat) : Bool := decide (tr.cell T_NODE r x = 1)

theorem one_iff {r x : Nat} : one tr x r = true ↔ tr.cell T_NODE r x = 1 := by simp [one]

theorem zero_of {r x : Nat} (hL : TableLocal Node.table tr T_NODE pub) (hr : r < tr.height T_NODE)
    (hx : x ∈ boolCols) (h : one tr x r = false) : tr.cell T_NODE r x = 0 :=
  bool01 hL hr hx (by simpa [one] using h)

theorem nodeSegFacts (hL : TableLocal Node.table tr T_NODE pub) :
    SegFacts (tr.height T_NODE) (one tr act) (one tr nf) (one tr nl) where
  first_act r hr h := by rw [one_iff] at h ⊢; exact ((rowFacts hL hr).2.2.2.1 h).1
  last_act r hr h := by rw [one_iff] at h ⊢; exact ((rowFacts hL hr).2.2.2.2.1 h).1
  cont r hr ha hl := by
    rw [one_iff] at ha
    have := inNode hL hr ha (zero_of hL (by omega) (by simp [boolCols]) hl)
    simp [one, this.1, this.2.1]
  next r hr hl ha := by
    rw [one_iff] at hl ha ⊢
    exact ((atEnd hL hr hl).2 ha).1
  pad r hr ha := by
    have := (afterInactive hL hr (zero_of hL (by omega) (by simp [boolCols]) ha)).1
    simp [one, this]
  start h0 := by simp [one, (firstRow hL h0).2.1]
  stop h0 ha := by rw [one_iff] at ha; rw [lastRow hL h0] at ha; exact absurd ha fp_zero_ne_one

/-- Field segments inside the node segment `(s, ℓ)` (offsets relative to `s`). -/
theorem fieldSegFacts (hL : TableLocal Node.table tr T_NODE pub) {s ℓ : Nat}
    (hseg : IsSeg (one tr act) (one tr nf) (one tr nl) s ℓ) (hH : s + ℓ ≤ tr.height T_NODE) :
    SegFacts ℓ (fun _ => true) (fun r => one tr fs (s + r)) (fun r => one tr fe (s + r)) where
  first_act _ _ _ := rfl
  last_act _ _ _ := rfl
  cont r hr _ hl := by
    have ha : tr.cell T_NODE (s + r) act = 1 := by
      have := hseg.2.2.2.1 (s + r) (by omega) (by omega); rwa [one_iff] at this
    have := (inField hL (r := s + r) (by omega) ha (zero_of hL (by omega) (by simp [boolCols]) hl)).2.2
    refine ⟨rfl, ?_⟩
    simp [one, show s + (r + 1) = s + r + 1 by omega, this]
  next r hr hl _ := by
    rw [one_iff] at hl ⊢
    have hnl : tr.cell T_NODE (s + r) nl = 0 :=
      zero_of hL (by omega) (by simp [boolCols]) (hseg.2.2.2.2.2 (s + r) (by omega) (by omega))
    rw [show s + (r + 1) = s + r + 1 by omega]
    exact (afterField hL (r := s + r) (by omega) hl hnl).2
  pad _ _ h := by simp at h
  start _ := by
    have h := hseg.2.1; rw [one_iff] at h
    rw [one_iff, Nat.add_zero]; exact ((rowFacts hL (by omega)).2.2.2.1 h).2.2.1
  stop h0 _ := by
    have h := hseg.2.2.1; rw [one_iff] at h
    rw [one_iff, show s + (ℓ - 1) = s + ℓ - 1 by omega]
    exact ((rowFacts hL (by omega)).2.2.2.2.1 h).2.1

end ZkFormal.Near.NodeProof
