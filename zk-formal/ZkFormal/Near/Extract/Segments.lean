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

namespace ZkFormal.Near

theorem segEnd_ge (segs : List (Nat × Nat)) (s0 : Nat) (hc : Consec s0 segs) : s0 ≤ segEnd s0 segs := by
  induction segs generalizing s0 with
  | nil => simp [segEnd]
  | cons p rest ih =>
    obtain ⟨s, ℓ⟩ := p
    obtain ⟨rfl, hc⟩ := hc
    have := ih (s + ℓ) hc
    simp only [segEnd]; omega

/-- Rows of consecutive segments. -/
theorem range'_segs (segs : List (Nat × Nat)) (s0 : Nat) (hc : Consec s0 segs) :
    List.range' s0 (segEnd s0 segs - s0) = segs.flatMap fun p => List.range' p.1 p.2 := by
  induction segs generalizing s0 with
  | nil => simp [segEnd]
  | cons p rest ih =>
    obtain ⟨s, ℓ⟩ := p
    obtain ⟨rfl, hc⟩ := hc
    have hle := segEnd_ge rest (s + ℓ) hc
    simp only [segEnd, List.flatMap_cons]
    rw [← ih (s + ℓ) hc]
    have : segEnd (s + ℓ) rest - s = ℓ + (segEnd (s + ℓ) rest - (s + ℓ)) := by omega
    rw [this, ← List.range'_append_1]

/-- Little-endian value of a digit list (base 256). -/
def le256 : List Nat → Nat
  | [] => 0
  | x :: xs => x + 256 * le256 xs

/-- **Carry chain.** If `s_j + 256·c_{j+1} = a_j + b_j + c_j` for every digit, then
`le256 s + 256^L · c_L = le256 a + le256 b + c_0`. -/
theorem carry_chain (s : List Nat) : ∀ (a b : List Nat) (c : Nat → Nat), a.length = s.length →
    b.length = s.length →
    (∀ j, j < s.length → s.getD j 0 + 256 * c (j + 1) = a.getD j 0 + b.getD j 0 + c j) →
    le256 s + 256 ^ s.length * c s.length = le256 a + le256 b + c 0 := by
  induction s with
  | nil =>
    intro a b c ha hb _
    rw [List.length_nil, List.length_eq_zero_iff] at ha hb
    subst ha; subst hb; simp [le256]
  | cons z s ih =>
    intro a b c ha hb h
    cases a with
    | nil => simp at ha
    | cons x a =>
    cases b with
    | nil => simp at hb
    | cons y b =>
    have h0 := h 0 (by simp)
    have ih' := ih a b (fun j => c (j + 1)) (by simpa using ha) (by simpa using hb)
      (fun j hj => by simpa using h (j + 1) (by simpa using hj))
    simp only [List.getD_cons_zero] at h0
    simp only [le256, List.length_cons, Nat.pow_succ]
    have : 256 ^ s.length * 256 * c (s.length + 1) = 256 * (256 ^ s.length * c (s.length + 1)) := by
      rw [Nat.mul_comm (256 ^ s.length) 256, Nat.mul_assoc]
    rw [this]
    omega

end ZkFormal.Near

namespace ZkFormal.Near

theorem const_of {α : Type} {f : Nat → α} {s ℓ : Nat}
    (hstep : ∀ r, s ≤ r → r + 1 < s + ℓ → f (r + 1) = f r) :
    ∀ r, s ≤ r → r < s + ℓ → f r = f s := by
  intro r h1 h2
  induction r with
  | zero => have : s = 0 := by omega
            subst this; rfl
  | succ r ih =>
    rcases Nat.lt_or_ge r s with h | h
    · have : s = r + 1 := by omega
      subst this; rfl
    · rw [hstep r h (by omega), ih h (by omega)]

end ZkFormal.Near

namespace ZkFormal.Near
theorem seg_le_end (segs : List (Nat × Nat)) (s0 : Nat) (hc : Consec s0 segs) :
    ∀ p ∈ segs, s0 ≤ p.1 ∧ p.1 + p.2 ≤ segEnd s0 segs := by
  induction segs generalizing s0 with
  | nil => simp
  | cons q rest ih =>
    obtain ⟨s, ℓ⟩ := q
    obtain ⟨rfl, hc⟩ := hc
    intro p hp
    have hge := segEnd_ge rest (s + ℓ) hc
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only [segEnd]; omega
    · have := ih (s + ℓ) hc p hp; simp only [segEnd]; omega

theorem range'_succ' (s ℓ : Nat) : List.range' s (ℓ + 1) = List.range' s ℓ ++ [s + ℓ] := by
  rw [← List.range'_append_1]; simp
end ZkFormal.Near

namespace ZkFormal.Near
theorem range'_split (A H : Nat) (h : A ≤ H) :
    List.range' 0 H = List.range' 0 A ++ List.range' A (H - A) := by
  have := @List.range'_append_1 0 A (H - A)
  simp only [Nat.zero_add] at this
  rw [this, Nat.add_sub_cancel' h]

theorem flatMap_nil_fun {α β : Type} (l : List α) : l.flatMap (fun _ => ([] : List β)) = [] := by
  induction l <;> simp_all
end ZkFormal.Near

namespace ZkFormal.Near
theorem consec_get (segs : List (Nat × Nat)) (s0 : Nat) (hc : Consec s0 segs) :
    ∀ t (h : t + 1 < segs.length), segs[t + 1].1 = segs[t].1 + segs[t].2 := by
  induction segs generalizing s0 with
  | nil => intro t h; simp at h
  | cons p rest ih =>
    obtain ⟨s, ℓ⟩ := p
    obtain ⟨rfl, hc⟩ := hc
    intro t h
    cases t with
    | zero =>
      cases rest with
      | nil => simp at h
      | cons q rest' => exact hc.1
    | succ t => exact ih (s + ℓ) hc t (by simpa using h)

theorem le256_eq_leNat (l : List Nat) (h : ∀ y ∈ l, y < 256) :
    NearSpec.leNat (l.map UInt8.ofNat) = le256 l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, NearSpec.leNat, le256]
    rw [ih (fun z hz => h z (by simp [hz]))]
    have hy := h y (by simp)
    simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hy]
end ZkFormal.Near

namespace ZkFormal.Near
/-- Row-wise lists over a segmented table: padding rows contribute nothing. -/
theorem flatMap_rows_segs {α : Type} (H : Nat) (segs : List (Nat × Nat)) (f : Nat → List α)
    (hc : Consec 0 segs) (hend : segEnd 0 segs ≤ H)
    (hpad : ∀ r, segEnd 0 segs ≤ r → r < H → f r = []) :
    (List.range H).flatMap f = segs.flatMap fun p => (List.range' p.1 p.2).flatMap f := by
  have hA := segEnd_ge segs 0 hc
  have e1 : List.range H = List.range' 0 (segEnd 0 segs - 0) ++
      List.range' (segEnd 0 segs) (H - segEnd 0 segs) := by
    rw [List.range_eq_range', Nat.sub_zero]; exact range'_split _ _ hend
  rw [e1, List.flatMap_append, range'_segs segs 0 hc, List.flatMap_assoc]
  have : (List.range' (segEnd 0 segs) (H - segEnd 0 segs)).flatMap f = [] := by
    have gen : ∀ len, segEnd 0 segs + len ≤ H → (List.range' (segEnd 0 segs) len).flatMap f = [] := by
      intro len
      induction len with
      | zero => intro _; rfl
      | succ len ih =>
        intro hl
        rw [range'_succ', List.flatMap_append, ih (by omega)]
        simp [hpad (segEnd 0 segs + len) (by omega) (by omega)]
    exact gen _ (by omega)
  rw [this, List.append_nil]
end ZkFormal.Near

namespace ZkFormal.Near
/-- `flatMap` over `range' s ℓ` of functions that are singletons there. -/
theorem flatMap_range'_single {α : Type} (f : Nat → List α) (g : Nat → α) (s ℓ : Nat)
    (h : ∀ j, j < ℓ → f (s + j) = [g j]) :
    (List.range' s ℓ).flatMap f = (List.range ℓ).map g := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [range'_succ', List.flatMap_append, ih (fun j hj => h j (by omega)),
      List.range_succ, List.map_append]
    simp [h ℓ (by omega)]

theorem flatMap_range'_nil {α : Type} (f : Nat → List α) (s ℓ : Nat)
    (h : ∀ j, j < ℓ → f (s + j) = []) : (List.range' s ℓ).flatMap f = [] := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [range'_succ', List.flatMap_append, ih (fun j hj => h j (by omega))]
    simp [h ℓ (by omega)]

theorem flatMap_segs {α : Type} (segs : List (Nat × Nat)) (F G : Nat × Nat → List α)
    (h : ∀ p ∈ segs, F p = G p) : segs.flatMap F = segs.flatMap G := by
  induction segs with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.flatMap_cons]
    rw [h p (by simp), ih (fun q hq => h q (by simp [hq]))]
end ZkFormal.Near

namespace ZkFormal.Near
theorem map_eq_flatMap {α β : Type} (l : List α) (f : α → β) : l.map f = l.flatMap fun a => [f a] := by
  induction l <;> simp_all
end ZkFormal.Near

namespace ZkFormal.Near
theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.flatMap_cons]
    refine List.Perm.trans (List.Perm.append_left _ ih) ?_
    simp only [List.append_assoc]
    apply List.Perm.append_left
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem range'_flatMap_pairs (s n : Nat) :
    List.range' s (2 * n) = (List.range n).flatMap fun j => [s + 2 * j, s + 2 * j + 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, ← List.range'_append_1, ih, List.range_succ,
      List.flatMap_append]
    simp [List.range', show s + 2 * n + 1 = s + (2 * n + 1) by omega]
end ZkFormal.Near
