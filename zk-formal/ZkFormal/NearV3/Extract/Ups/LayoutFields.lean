import ZkFormal.NearV3.Extract.Ups.Layout
import ZkFormal.NearV3.Extract.Ups.FieldRows

/-!
# ZkFormal.NearV3.Extract.Ups.LayoutFields — the fields of a node part

Inside a node part (rows `o … o+ℓ−1`), the rows split into consecutive fields (`fs … fe`),
each with a constant state and `idx = 0, 1, …`; the first field is a `TAG` field and the last
one a `MEM` field ending at the part's last row.  Segment constants are constant over the
whole segment.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- A field: rows `r0 … r0+L−1`. -/
structure UField (s : UpsSeg) (r0 L : Nat) : Prop where
  pos : 0 < L
  st : ∀ k, k < L → ∀ x ∈ states, s.row (r0 + k) x = s.row r0 x
  idx : ∀ k, k < L → s.row (r0 + k) idx = k
  fs : ∀ k, k < L → (s.row (r0 + k) fs = 1 ↔ k = 0)
  fe : ∀ k, k < L → (s.row (r0 + k) fe = 1 ↔ k + 1 = L)

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

theorem fieldR {r : Nat} (hr : r < s.rows.length) : FieldRowP (s.row r) (s.next r) :=
  fieldRow (okRow hw hs hr) (rowLt hw hs r) (nextLt hw hs r)

theorem fieldI {r : Nat} (hr : r + 1 < s.rows.length) : FieldRowP (s.row r) (s.row (r + 1)) :=
  fieldRow (okIn hw hs hr) (rowLt hw hs r) (rowLt hw hs (r + 1))

/-- Segment constants hold over the whole segment. -/
theorem segConstAll {i : Nat} (hi : i < s.rows.length) {x : Nat} (hx : x ∈ segConst) : s.row i x = s.row 0 x := by
  have := const_of (f := fun r => s.row r x) (s := 0) (ℓ := s.rows.length) (fun r _ h2 => by
    have hn : r + 1 < s.rows.length := by omega
    exact sconst (okIn hw hs hn) (rowLt hw hs _) (rowLt hw hs _) (hw.act s hs r (by omega))
      (notEnd hw hs hn) hx) i (by omega) (by omega)
  simpa using this

variable {o ℓ : Nat} (hℓ : 0 < ℓ) (hle : o + ℓ ≤ s.rows.length)
  (hq : ∀ d, d < ℓ → s.row (o + d) qb = 1 ∧ (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ))
include hℓ hle hq

theorem partFieldFacts :
    SegFacts ℓ (fun _ => true) (colAt s fs o) (colAt s fe o) where
  first_act _ _ _ := rfl
  last_act _ _ _ := rfl
  cont r hr _ hl := by
    simp only [colAt, decide_eq_false_iff_not] at hl ⊢
    have F := fieldI hw hs (r := o + r) (by omega)
    have hfe : s.row (o + r) fe = 0 := F.2.1.resolve_right hl
    refine ⟨trivial, ?_⟩
    rw [show o + (r + 1) = o + r + 1 by omega]
    have := (F.2.2.2.2.1 (hq r (by omega)).1 hfe).2.2
    omega
  next r hr hl _ := by
    simp only [colAt, decide_eq_true_eq] at hl ⊢
    have F := fieldI hw hs (r := o + r) (by omega)
    have hpl : s.row (o + r) pl = 0 :=
      (plBool hw hs (by omega)).resolve_right (fun h => by have := ((hq r (by omega)).2.2.1 h); omega)
    rw [show o + (r + 1) = o + r + 1 by omega]
    exact (F.2.2.2.2.2.1 (hq r (by omega)).1 hl hpl).2
  pad _ _ h := by simp at h
  start _ := by
    simp only [colAt, decide_eq_true_eq, Nat.add_zero]
    have F := fieldR hw hs (r := o) (by omega)
    have h := hq 0 hℓ
    simp only [Nat.add_zero] at h
    exact (F.2.2.1 (h.2.1.2 trivial) h.1).2
  stop _ _ := by
    simp only [colAt, decide_eq_true_eq]
    have F := fieldR hw hs (r := o + (ℓ - 1)) (by omega)
    have h := hq (ℓ - 1) (by omega)
    have hp := h.2.2.2 (by omega)
    have e := F.2.2.2.2.2.2 h.1
    have := stBool (okRow hw hs (i := o + (ℓ - 1)) (by omega)) (rowLt hw hs _) (x := sMEM) (by simp [states])
    rcases F.2.1 with h0 | h0
    · rw [h0] at e; omega
    · rw [show o + (ℓ - 1) = o + (ℓ - 1) from rfl]; exact h0

/-- A field of the part (offset `p`, length `L`). -/
theorem fieldOf {p L : Nat} (hf : IsSeg (fun _ => true) (colAt s fs o) (colAt s fe o) p L) (hpL : p + L ≤ ℓ) :
    UField s (o + p) L := by
  obtain ⟨hpos, hfs, hfe, -, hnf, hnfe⟩ := hf
  simp only [colAt, decide_eq_true_eq, decide_eq_false_iff_not] at hfs hfe hnf hnfe
  have hm := lenLe hw hs
  have hfe0 : ∀ k, k + 1 < L → s.row (o + p + k) fe = 0 := fun k hk => by
    have := hnfe (p + k) (by omega) (by omega)
    rw [← Nat.add_assoc] at this
    exact ((fieldR hw hs (r := o + p + k) (by omega)).2.1).resolve_right this
  have st := fun k (hk : k + 1 < L) =>
    (fieldI hw hs (r := o + p + k) (by omega)).2.2.2.2.1 (by rw [Nat.add_assoc]; exact (hq (p + k) (by omega)).1) (hfe0 k hk)
  have hidx0 : s.row (o + p) idx = 0 := (fieldR hw hs (r := o + p) (by omega)).2.2.2.1 hfs
  refine ⟨hpos, fun k hk x hx => ?_, fun k hk => ?_, fun k hk => ⟨fun h => ?_, fun h => ?_⟩,
    fun k hk => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact const_of (f := fun r => s.row r x) (s := o + p) (ℓ := L) (fun r h1 h2 => by
      have := (st (r - (o + p)) (by omega)).1 x hx
      rwa [show o + p + (r - (o + p)) = r by omega] at this) (o + p + k) (by omega) (by omega)
  · have hc := counter_of (f := fun r => ((s.row r idx : Nat) : Fp)) (s := o + p) (ℓ := L) (v0 := 0)
      (by simp only [hidx0]) (fun r h1 h2 => by
        have := (st (r - (o + p)) (by omega)).2.1
        rwa [show o + p + (r - (o + p)) = r by omega] at this) (o + p + k) (by omega) (by omega)
    simp only [show 0 + (o + p + k - (o + p)) = k by omega] at hc
    exact natv (rowLt hw hs _ _) (by have := P_big; omega) hc
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact h0
    · exfalso; have := hnf (p + k) (by omega) (by omega); rw [← Nat.add_assoc] at this; exact this h
  · subst h; simpa using hfs
  · rcases Nat.lt_or_ge (k + 1) L with h' | h'
    · rw [hfe0 k h'] at h; omega
    · omega
  · rw [show o + p + k = o + (p + L - 1) by omega]; exact hfe

/-- **The fields of a node part.** -/
theorem partFields : ∃ fl : List (Nat × Nat), Consec 0 fl ∧ segEnd 0 fl = ℓ ∧ 0 < fl.length ∧
    ∀ q (hq' : q < fl.length), UField s (o + fl[q].1) fl[q].2 ∧ fl[q].1 + fl[q].2 ≤ ℓ := by
  obtain ⟨fl, hc, hend, hall, hpad⟩ := segments_of (partFieldFacts hw hs hℓ hle hq) hℓ
  have hcov : segEnd 0 fl = ℓ := by
    rcases Nat.lt_or_ge (segEnd 0 fl) ℓ with h | h
    · have := hpad (segEnd 0 fl) (Nat.le_refl _) h; simp at this
    · omega
  have hpos : 0 < fl.length := by
    rcases Nat.eq_zero_or_pos fl.length with h | h
    · rw [List.length_eq_zero_iff] at h; subst h; simp [segEnd] at hcov; omega
    · exact h
  refine ⟨fl, hc, hcov, hpos, fun q hq' => ?_⟩
  have hle' := consec_mem_lt fl 0 hc q hq'
  exact ⟨fieldOf hw hs hℓ hle hq (hall _ (List.getElem_mem hq')) (by omega), by omega⟩

end

end ZkFormal.NearV3.UpsRows
