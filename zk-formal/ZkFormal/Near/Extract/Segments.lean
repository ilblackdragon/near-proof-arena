import ZkFormal.Near.Extract.Eval

/-!
# ZkFormal.Near.Extract.Segments — rows of a table as a sequence of segments

All NEAR tables share one row shape: active rows form a prefix, split into
segments (`first … last`), followed by inactive rows.  `segments_of` turns
the local transition facts into an explicit list of segment starts and
lengths; `counter_of` turns a `+1` counter into the row offset.  Row
predicates are `Bool`-valued functions of the row index.
-/

namespace ZkFormal.Near

/-- Transition facts of a segmented table of height `H`. -/
structure SegFacts (H : Nat) (act first last : Nat → Bool) : Prop where
  first_act : ∀ r, r < H → first r = true → act r = true
  last_act : ∀ r, r < H → last r = true → act r = true
  /-- inside a segment the next row is active and not a start -/
  cont : ∀ r, r + 1 < H → act r = true → last r = false → act (r + 1) = true ∧ first (r + 1) = false
  /-- after a segment end, an active row starts a segment -/
  next : ∀ r, r + 1 < H → last r = true → act (r + 1) = true → first (r + 1) = true
  /-- inactive rows are followed by inactive rows -/
  pad : ∀ r, r + 1 < H → act r = false → act (r + 1) = false
  /-- row 0 starts a segment -/
  start : 0 < H → first 0 = true
  /-- the last row is not inside a segment -/
  stop : 0 < H → act (H - 1) = true → last (H - 1) = true

/-- Segment `(s, ℓ)`: rows `s … s+ℓ-1`, `first` exactly at `s`, `last` exactly at `s+ℓ-1`. -/
def IsSeg (act first last : Nat → Bool) (s ℓ : Nat) : Prop :=
  0 < ℓ ∧ first s = true ∧ last (s + ℓ - 1) = true ∧
  (∀ r, s ≤ r → r < s + ℓ → act r = true) ∧
  (∀ r, s < r → r < s + ℓ → first r = false) ∧
  (∀ r, s ≤ r → r + 1 < s + ℓ → last r = false)

/-- Starts are consecutive from `s0`. -/
def Consec : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | s0, (s, ℓ) :: rest => s = s0 ∧ Consec (s0 + ℓ) rest

def segEnd : Nat → List (Nat × Nat) → Nat
  | s0, [] => s0
  | _, (s, ℓ) :: rest => segEnd (s + ℓ) rest

theorem exists_least {p : Nat → Prop} (h : ∃ d, p d) : ∃ d, p d ∧ ∀ e, e < d → ¬ p e := by
  obtain ⟨d, hd⟩ := h
  induction d using Nat.strongRecOn with
  | ind d ih =>
    by_cases hx : ∃ e, e < d ∧ p e
    · obtain ⟨e, he, hpe⟩ := hx; exact ih e he hpe
    · exact ⟨d, hd, fun e he hpe => hx ⟨e, he, hpe⟩⟩

/-- From row `s` (a segment start, active), the segment ends somewhere. -/
theorem seg_from {H : Nat} {act first last : Nat → Bool} (hf : SegFacts H act first last)
    (s : Nat) (hs : s < H) (hfs : first s = true) :
    ∃ ℓ, s + ℓ ≤ H ∧ IsSeg act first last s ℓ := by
  -- walk forward until `last`
  have key : ∀ d, s + d < H → (∀ e, e < d → last (s + e) = false) →
      (∀ e, e ≤ d → act (s + e) = true) ∧ (∀ e, 0 < e → e ≤ d → first (s + e) = false) := by
    intro d
    induction d with
    | zero =>
      intro _ _
      exact ⟨fun e he => by
        have : e = 0 := by omega
        subst this; exact hf.first_act s hs hfs, fun e h0 h => by omega⟩
    | succ d ih =>
      intro hd hl
      obtain ⟨ha, hfi⟩ := ih (by omega) (fun e he => hl e (by omega))
      have hc := hf.cont (s + d) (by omega) (ha d (Nat.le_refl _)) (hl d (by omega))
      refine ⟨fun e he => ?_, fun e h0 he => ?_⟩
      · rcases Nat.lt_or_ge e (d + 1) with h | h
        · exact ha e (by omega)
        · have : e = d + 1 := by omega
          subst this; rw [← Nat.add_assoc]; exact hc.1
      · rcases Nat.lt_or_ge e (d + 1) with h | h
        · exact hfi e h0 (by omega)
        · have : e = d + 1 := by omega
          subst this; rw [← Nat.add_assoc]; exact hc.2
  have hex : ∃ d, s + d < H ∧ last (s + d) = true := by
    refine Classical.byContradiction fun hne => ?_
    have hall : ∀ e, s + e < H → last (s + e) = false := fun e he => by
      cases h : last (s + e)
      · rfl
      · exact absurd ⟨e, he, h⟩ hne
    have h1 : s + (H - 1 - s) = H - 1 := by omega
    have ha := (key (H - 1 - s) (by omega) (fun e he => hall e (by omega))).1 (H - 1 - s) (Nat.le_refl _)
    rw [h1] at ha
    have h2 := hall (H - 1 - s) (by omega)
    rw [h1, hf.stop (by omega) ha] at h2
    cases h2
  obtain ⟨d, ⟨hdH, hld⟩, hmin⟩ := exists_least hex
  have hl' : ∀ e, e < d → last (s + e) = false := fun e he => by
    cases h : last (s + e)
    · rfl
    · exact absurd ⟨by omega, h⟩ (hmin e he)
  obtain ⟨ha, hfi⟩ := key d hdH hl'
  refine ⟨d + 1, by omega, by omega, hfs, ?_, ?_, ?_, ?_⟩
  · have : s + (d + 1) - 1 = s + d := by omega
    rw [this]; exact hld
  · intro r h1 h2
    have := ha (r - s) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  · intro r h1 h2
    have := hfi (r - s) (by omega) (by omega); rwa [Nat.add_sub_cancel' (Nat.le_of_lt h1)] at this
  · intro r h1 h2
    have := hl' (r - s) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- **Segment decomposition.**  Rows `0 … A−1` are the consecutive segments
`segs`, rows `A … H−1` are inactive. -/
theorem segments_of {H : Nat} {act first last : Nat → Bool} (hf : SegFacts H act first last)
    (hH : 0 < H) :
    ∃ segs : List (Nat × Nat), Consec 0 segs ∧ segEnd 0 segs ≤ H ∧
      (∀ p ∈ segs, IsSeg act first last p.1 p.2) ∧
      (∀ r, segEnd 0 segs ≤ r → r < H → act r = false) := by
  -- build from row `s` (a start, or ≥ H, or inactive)
  have build : ∀ fuel s, H - s ≤ fuel → (s < H → act s = true → first s = true) →
      ∃ segs : List (Nat × Nat), Consec s segs ∧ segEnd s segs ≤ max s H ∧
        (∀ p ∈ segs, IsSeg act first last p.1 p.2) ∧
        (∀ r, segEnd s segs ≤ r → r < H → act r = false) := by
    intro fuel
    induction fuel with
    | zero =>
      intro s hs _
      exact ⟨[], trivial, by simp [segEnd]; omega, by simp, fun r h1 h2 => by simp [segEnd] at h1; omega⟩
    | succ f ih =>
      intro s hs hstart
      by_cases hsH : s < H
      · cases hact : act s
        · -- inactive from here on
          refine ⟨[], trivial, by simp [segEnd]; omega, by simp, fun r h1 h2 => ?_⟩
          simp only [segEnd] at h1
          have : ∀ e, s + e < H → act (s + e) = false := by
            intro e; induction e with
            | zero => intro _; simpa using hact
            | succ e ihe => intro he; rw [← Nat.add_assoc]; exact hf.pad _ he (ihe (by omega))
          have := this (r - s) (by omega); rwa [Nat.add_sub_cancel' h1] at this
        · obtain ⟨ℓ, hℓH, hseg⟩ := seg_from hf s hsH (hstart hsH hact)
          obtain ⟨segs, hc, he, hall, hpad⟩ := ih (s + ℓ) (by have := hseg.1; omega) (fun h1 h2 => by
            have hl := hseg.2.2.1
            have : s + ℓ - 1 + 1 = s + ℓ := by have := hseg.1; omega
            have := hf.next (s + ℓ - 1) (by omega) hl (by rw [this]; exact h2)
            rwa [show s + ℓ - 1 + 1 = s + ℓ by have := hseg.1; omega] at this)
          refine ⟨(s, ℓ) :: segs, ⟨rfl, hc⟩, ?_, ?_, ?_⟩
          · simp only [segEnd]; omega
          · intro p hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hseg
            · exact hall p hp
          · intro r h1 h2; exact hpad r (by simpa [segEnd] using h1) h2
      · exact ⟨[], trivial, by simp [segEnd]; omega, by simp, fun r h1 h2 => by simp [segEnd] at h1; omega⟩
  obtain ⟨segs, hc, he, hall, hpad⟩ := build H 0 (by omega) (fun _ _ => hf.start hH)
  exact ⟨segs, hc, by simpa using he, hall, hpad⟩

/-! ## Counters -/

/-- A field counter that is `v0` at row `s` and grows by one per row equals
`v0 + (r − s)` as long as that stays below `P`. -/
theorem counter_of {f : Nat → ZkFormal.Algebra.Fp} {s ℓ v0 : Nat} (h0 : f s = (v0 : ZkFormal.Algebra.Fp))
    (hstep : ∀ r, s ≤ r → r + 1 < s + ℓ → f (r + 1) = f r + 1) :
    ∀ r, s ≤ r → r < s + ℓ → f r = ((v0 + (r - s) : Nat) : ZkFormal.Algebra.Fp) := by
  intro r h1 h2
  induction r with
  | zero => have : s = 0 := by omega
            subst this; simpa using h0
  | succ r ih =>
    rcases Nat.lt_or_ge r s with h | h
    · have : s = r + 1 := by omega
      subst this; simpa using h0
    · rw [hstep r h (by omega), ih h (by omega)]
      have : v0 + (r + 1 - s) = v0 + (r - s) + 1 := by omega
      rw [this, natCast_add (v0 + (r - s)) 1]; rfl

end ZkFormal.Near
