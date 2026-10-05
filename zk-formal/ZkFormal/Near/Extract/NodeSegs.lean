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

namespace ZkFormal.Near.NodeProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Node

variable {tr : Trace Fp} {pub : List Fp}

/-- A field: rows `r0 … r0+L-1`, starting at `fs`, ending at `fe`. -/
structure Field (tr : Trace Fp) (r0 L : Nat) : Prop where
  pos : 0 < L
  act : ∀ k, k < L → tr.cell T_NODE (r0 + k) act = 1
  st : ∀ k, k < L → ∀ x ∈ states, tr.cell T_NODE (r0 + k) x = tr.cell T_NODE r0 x
  idx : ∀ k, k < L → tr.cell T_NODE (r0 + k) idx = ((k : Nat) : Fp)
  fs : ∀ k, k < L → (tr.cell T_NODE (r0 + k) fs = 1 ↔ k = 0)
  fe : ∀ k, k < L → (tr.cell T_NODE (r0 + k) fe = 1 ↔ k + 1 = L)

theorem field_of (hL : TableLocal Node.table tr T_NODE pub) {s ℓ o L : Nat}
    (hseg : IsSeg (one tr act) (one tr nf) (one tr nl) s ℓ) (hH : s + ℓ ≤ tr.height T_NODE)
    (hf : IsSeg (fun _ => true) (fun r => one tr fs (s + r)) (fun r => one tr fe (s + r)) o L)
    (hoL : o + L ≤ ℓ) : Field tr (s + o) L := by
  have hP : tr.height T_NODE < P := by have := height_le hL; unfold P; omega
  obtain ⟨hpos, hfs, hfe, -, hnf, hnfe⟩ := hf
  have hA : ∀ k, k < L → tr.cell T_NODE (s + o + k) act = 1 := fun k hk => by
    have := hseg.2.2.2.1 (s + o + k) (by omega) (by omega); rwa [one_iff] at this
  have hfe0 : ∀ k, k + 1 < L → tr.cell T_NODE (s + o + k) fe = 0 := fun k hk => by
    have := hnfe (o + k) (by omega) (by omega)
    simp only at this
    rw [show s + (o + k) = s + o + k by omega] at this
    exact zero_of hL (by omega) (by simp [boolCols]) this
  have hstep := fun k (hk : k + 1 < L) => inField hL (r := s + o + k) (by omega) (hA k (by omega)) (hfe0 k hk)
  have hfs0 : tr.cell T_NODE (s + o) fs = 1 := by rw [one_iff] at hfs; exact hfs
  -- idx = 0 at the field start
  have hidx0 : tr.cell T_NODE (s + o) idx = 0 := by
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · subst h0
      have hnfs := hseg.2.1; rw [one_iff] at hnfs
      rw [Nat.add_zero]; exact ((rowFacts hL (by omega)).2.2.2.1 hnfs).2.2.2.2
    · -- the previous row ends a field (a row before `o` in the node)
      have hprev : tr.cell T_NODE (s + o - 1) fe = 1 := by
        rcases isBool hL (r := s + o - 1) (by omega) (x := fe) (by simp [boolCols]) with h | h
        · have := (inField hL (r := s + o - 1) (by omega) (by
              have := hseg.2.2.2.1 (s + o - 1) (by omega) (by omega); rwa [one_iff] at this) h).2.2
          rw [show s + o - 1 + 1 = s + o by omega, hfs0] at this; exact absurd this fp_one_ne_zero
        · exact h
      have hnl : tr.cell T_NODE (s + o - 1) nl = 0 :=
        zero_of hL (by omega) (by simp [boolCols]) (hseg.2.2.2.2.2 (s + o - 1) (by omega) (by omega))
      have := (afterField hL (r := s + o - 1) (by omega) hprev hnl).1
      rwa [show s + o - 1 + 1 = s + o by omega] at this
  have hidx := counter_of (f := fun q => tr.cell T_NODE q idx) (s := s + o) (ℓ := L) (v0 := 0) (by simp [hidx0]; rfl)
    (fun q h1 h2 => by
      have := (hstep (q - (s + o)) (by omega)).2.1; rwa [show s + o + (q - (s + o)) = q by omega] at this)
  refine ⟨hpos, hA, fun k hk x hx => ?_, fun k hk => ?_, fun k hk => ⟨fun h => ?_, fun h => ?_⟩,
    fun k hk => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := const_of (f := fun q => tr.cell T_NODE q x) (s := s + o) (ℓ := L) (fun q h1 h2 => by
      have := (hstep (q - (s + o)) (by omega)).1 x hx; rwa [show s + o + (q - (s + o)) = q by omega] at this)
    exact this (s + o + k) (by omega) (by omega)
  · have := hidx (s + o + k) (by omega) (by omega); simpa [show s + o + k - (s + o) = k by omega] using this
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact h0
    · exfalso
      have := hnf (o + k) (by omega) (by omega)
      simp only at this
      rw [show s + (o + k) = s + o + k by omega] at this
      simp only [one, decide_eq_false_iff_not] at this
      exact this h
  · subst h; simpa using hfs0
  · rcases Nat.lt_or_ge (k + 1) L with h' | h'
    · rw [hfe0 k h'] at h; exact absurd h fp_zero_ne_one
    · omega
  · rw [one_iff] at hfe
    rw [show s + o + k = s + (o + L - 1) by omega]; exact hfe

end ZkFormal.Near.NodeProof
