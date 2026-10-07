import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractUnits

/-! Candidate source units have exactly1,32,or64 rows. Uses the checked log24
logical reconstruction bound, not the old source table cap. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof

open SrcpProof (isOne uAct uFirst uLast)
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

abbrev IsU (tr : Trace Fp) (tt s ℓ : Nat) : Prop := IsSeg (uAct tr tt) (uFirst tr tt) (uLast tr tt) s ℓ

section
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

theorem hP : tr.height tt < P := by
  have hh := hL.log_le
  change tr.log tt ≤ 24 at hh
  have hb : tr.height tt ≤ 2^24 := Nat.pow_le_pow_right (by decide) hh
  unfold P
  omega

theorem rootUnit {s ℓ : Nat} (hu : IsU tr tt s ℓ) (hrt : tr.cell tt s rt = 1) : ℓ = 1 := by
  obtain ⟨hpos, -, -, -, -, hlast⟩ := hu
  rcases Nat.lt_or_ge 1 ℓ with h | h
  · have := hlast s (Nat.le_refl _) (by omega)
    simp [uLast, isOne, hrt] at this
  · omega

theorem rt_bool {r : Nat} (hr : r < tr.height tt) (h : ¬ tr.cell tt r rt = 1) : tr.cell tt r rt = 0 := by
  rcases isBool hL hr (x := rt) (by simp [SrcpProof.bools]) with h' | h'
  · exact h'
  · exact absurd h' h

/-- Rows of a segment unit. -/
theorem segRows {s ℓ : Nat} (hu : IsU tr tt s ℓ) (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0) :
    tr.cell tt s sf = 1 ∧ tr.cell tt s wf = 1 ∧ tr.cell tt s wn = 0 ∧ tr.cell tt s pw = 0 ∧
    tr.cell tt (s + ℓ - 1) sl = 1 ∧ tr.cell tt (s + ℓ - 1) wl = 1 ∧
    ∀ o, o < ℓ → tr.cell tt (s + o) sg = 1 ∧ tr.cell tt (s + o) rt = 0 ∧
      (o + 1 < ℓ → tr.cell tt (s + o) sl = 0) ∧
      (∀ x ∈ listConst, tr.cell tt (s + o) x = tr.cell tt s x) ∧
      (∀ x ∈ segConst, tr.cell tt (s + o) x = tr.cell tt s x) := by
  obtain ⟨hpos, hfs, hle, hact, hfirst, hlast⟩ := hu
  have hsf : tr.cell tt s sf = 1 := by
    simp only [uFirst, isOne, Bool.or_eq_true, decide_eq_true_eq] at hfs
    rcases hfs with h | h
    · rw [hrt] at h; exact absurd h (by decide)
    · exact h
  have hwf := (row_shape hL (r := s) (by omega)).1
  have hsfe := (row_shape hL (r := s) (by omega)).2.2.1
  have bw := isBool hL (r := s) (by omega) (x := wf) (by simp [SrcpProof.bools])
  have bn := isBool hL (r := s) (by omega) (x := wn) (by simp [SrcpProof.bools])
  have hwf1 : tr.cell tt s wf = 1 := by rcases bw with h | h <;> rw [hsfe, h] at hsf <;> grind
  have hwn0 : tr.cell tt s wn = 0 := by rcases bn with h | h <;> rw [hsfe, hwf1, h] at hsf <;> grind
  have hrows : ∀ o, o < ℓ → tr.cell tt (s + o) sg = 1 ∧ tr.cell tt (s + o) rt = 0 := by
    intro o ho
    have ha := hact (s + o) (by omega) (by omega)
    have hr0 : tr.cell tt (s + o) rt = 0 := by
      by_cases h0 : o = 0
      · subst h0; simpa using hrt
      · have := hfirst (s + o) (by omega) (by omega)
        simp only [uFirst, Bool.or_eq_false_iff] at this
        exact zero_of_not_one hL (by omega) (by simp [SrcpProof.bools]) this.1
    simp only [uAct, isOne, Bool.or_eq_true, decide_eq_true_eq, hr0] at ha
    rcases ha with h | h
    · exact absurd h (by decide)
    · exact ⟨h, hr0⟩
  have hsl0 : ∀ o, o + 1 < ℓ → tr.cell tt (s + o) sl = 0 := fun o ho => by
    have := hlast (s + o) (by omega) (by omega)
    simp only [uLast, Bool.or_eq_false_iff] at this
    exact zero_of_not_one hL (by omega) (by simp [SrcpProof.bools]) this.2
  have hstep := fun o (ho : o + 1 < ℓ) => inSeg hL (r := s + o) (by omega) (hrows o (by omega)).1 (hsl0 o ho)
  have hend : tr.cell tt (s + ℓ - 1) sl = 1 := by
    have := hle; simp only [uLast, isOne, Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · rw [show s + ℓ - 1 = s + (ℓ - 1) by omega, (hrows (ℓ - 1) (by omega)).2] at h; exact absurd h (by decide)
    · exact h
  have hwl : tr.cell tt (s + ℓ - 1) wl = 1 := by
    have hsle := (row_shape hL (r := s + ℓ - 1) (by omega)).2.2.2
    rcases isBool hL (r := s + ℓ - 1) (by omega) (x := wl) (by simp [SrcpProof.bools]) with h | h
    · rw [hsle, h] at hend; grind
    · exact h
  refine ⟨hsf, hwf1, hwn0, (hwf hwf1).2, hend, hwl, fun o ho => ⟨(hrows o ho).1, (hrows o ho).2,
    hsl0 o, fun x hx => ?_, fun x hx => ?_⟩⟩
  · have := const_of (f := fun r => tr.cell tt r x) (s := s) (ℓ := ℓ) (fun r h1 h2 => by
      have := (hstep (r - s) (by omega)).2.2.1 x hx; rwa [show s + (r - s) = r by omega] at this)
      (s + o) (by omega) (by omega)
    exact this
  · have := const_of (f := fun r => tr.cell tt r x) (s := s) (ℓ := ℓ) (fun r h1 h2 => by
      have := (hstep (r - s) (by omega)).2.2.2 x hx; rwa [show s + (r - s) = r by omega] at this)
      (s + o) (by omega) (by omega)
    exact this

/-- A window run inside a segment unit, before its first `wl`. -/
theorem winRun {s ℓ w : Nat} (hH : s + ℓ ≤ tr.height tt)
    (hsg : ∀ o, o < ℓ → tr.cell tt (s + o) sg = 1) (hw : s ≤ w) (hpw : tr.cell tt w pw = 0) :
    ∀ d, w + d < s + ℓ → (∀ d', d' < d → tr.cell tt (w + d') wl = 0) →
      tr.cell tt (w + d) pw = ((d : Nat) : Fp) ∧ tr.cell tt (w + d) wn = tr.cell tt w wn ∧
      (0 < d → tr.cell tt (w + d) wf = 0) ∧
      ∀ x, x + d < 32 → tr.cell tt (w + d) (reg x) = tr.cell tt w (reg (x + d)) := by
  intro d
  induction d with
  | zero => intro _ _; exact ⟨by rw [Nat.add_zero, hpw]; rfl, rfl, fun h => absurd h (by omega), fun x _ => rfl⟩
  | succ d ih =>
    intro hd hwl
    obtain ⟨i1, i2, -, i4⟩ := ih (by omega) (fun d' h => hwl d' (by omega))
    have hs := hsg (w + d - s) (by omega)
    rw [show s + (w + d - s) = w + d by omega] at hs
    obtain ⟨n1, n2, n3, n4⟩ := inWin hL (r := w + d) (by omega) hs (hwl d (by omega))
    rw [show w + (d + 1) = w + d + 1 by omega]
    refine ⟨by rw [n2, i1, natCast_add]; rfl, by rw [n3, i2], fun _ => n1, fun x hx => ?_⟩
    rw [n4 x (by omega), i4 (x + 1) (by omega), show x + 1 + d = x + (d + 1) by omega]

/-- The first `wl` of a window starting at `w` (inside a unit ending with `wl`) is at `w + 31`. -/
theorem winEnd {s ℓ w : Nat} (hH : s + ℓ ≤ tr.height tt)
    (hsg : ∀ o, o < ℓ → tr.cell tt (s + o) sg = 1) (hend : tr.cell tt (s + ℓ - 1) wl = 1)
    (hw : s ≤ w) (hwℓ : w < s + ℓ) (hpw : tr.cell tt w pw = 0) :
    w + 31 < s + ℓ ∧ tr.cell tt (w + 31) wl = 1 ∧ ∀ d', d' < 31 → tr.cell tt (w + d') wl = 0 := by
  have hex : ∃ d, w + d < s + ℓ ∧ tr.cell tt (w + d) wl = 1 :=
    ⟨s + ℓ - 1 - w, by omega, by rw [show w + (s + ℓ - 1 - w) = s + ℓ - 1 by omega]; exact hend⟩
  obtain ⟨d, ⟨hd, hd1⟩, hmin⟩ := exists_least hex
  have hz : ∀ d', d' < d → tr.cell tt (w + d') wl = 0 := fun d' h => by
    rcases isBool hL (r := w + d') (by omega) (x := wl) (by simp [SrcpProof.bools]) with h' | h'
    · exact h'
    · exact absurd ⟨by omega, h'⟩ (hmin d' h)
  have hpwd := (winRun hL hH hsg hw hpw d hd hz).1
  have hwl := (row_shape hL (r := w + d) (by omega)).2.1
  have e := (hwl hd1).2
  rw [hpwd] at e
  have hP' := hP hL
  have : d = 31 := ofNat_inj (by omega) (by unfold P; omega) e
  subst this
  exact ⟨hd, hd1, hz⟩

/-- Shape of a segment unit. -/
theorem segShape {s ℓ : Nat} (hu : IsU tr tt s ℓ) (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0) :
    (tr.cell tt s lf = 1 ∧ ℓ = 32 ∨ tr.cell tt s lf = 0 ∧ ℓ = 64) ∧
    ∀ o, o < ℓ → tr.cell tt (s + o) pw = (((o % 32 : Nat)) : Fp) ∧
      tr.cell tt (s + o) wn = (if o < 32 then 0 else 1) ∧
      tr.cell tt (s + o) wf = (if o % 32 = 0 then 1 else 0) ∧
      ∀ x, x + o % 32 < 32 → tr.cell tt (s + o) (reg x) = tr.cell tt (s + o - o % 32) (reg (x + o % 32)) := by
  obtain ⟨hsf, hwf, hwn, hpw, hsl, hwle, hrows⟩ := segRows hL hu hH hrt
  have hpos := hu.1
  have hsg := fun o ho => (hrows o ho).1
  obtain ⟨e1, e2, e3⟩ := winEnd hL hH hsg hwle (Nat.le_refl s) (by omega) hpw
  have run1 := winRun hL hH hsg (Nat.le_refl s) hpw
  have hlfB := isBool hL (r := s) (by omega) (x := lf) (by simp [SrcpProof.bools])
  -- the end of the first window
  have hlf31 : tr.cell tt (s + 31) lf = tr.cell tt s lf :=
    (hrows 31 (by omega)).2.2.2.2 lf (by simp [segConst])
  have hwn31 : tr.cell tt (s + 31) wn = 0 := by
    rw [(run1 31 (by omega) e3).2.1, hwn]
  have hsl31 := (row_shape hL (r := s + 31) (by omega)).2.2.2
  -- window 1 rows
  have w1 : ∀ o, o < 32 → o < ℓ → tr.cell tt (s + o) pw = (((o % 32 : Nat)) : Fp) ∧
      tr.cell tt (s + o) wn = (if o < 32 then 0 else 1) ∧
      tr.cell tt (s + o) wf = (if o % 32 = 0 then 1 else 0) ∧
      ∀ x, x + o % 32 < 32 → tr.cell tt (s + o) (reg x) = tr.cell tt (s + o - o % 32) (reg (x + o % 32)) := by
    intro o ho1 ho2
    obtain ⟨r1, r2, r3, r4⟩ := run1 o (by omega) (fun d' h => e3 d' (by omega))
    rw [Nat.mod_eq_of_lt ho1, if_pos ho1, r2, hwn, show s + o - o = s by omega]
    refine ⟨r1, rfl, ?_, r4⟩
    by_cases h0 : o = 0
    · subst h0; simpa using hwf
    · rw [if_neg h0]; exact r3 (by omega)
  rcases hlfB with hl0 | hl1
  · -- path segment: a second window
    have hsl31' : tr.cell tt (s + 31) sl = 0 := by rw [hsl31, e2, hwn31, hlf31, hl0]; grind
    have hℓ : 32 < ℓ := by
      rcases Nat.lt_or_ge 32 ℓ with h | h
      · exact h
      · have : ℓ = 32 := by omega
        subst this
        rw [show s + 32 - 1 = s + 31 by omega, hsl31'] at hsl; exact absurd hsl (by decide)
    obtain ⟨f1, f2⟩ := winSwitch hL (r := s + 31) (by omega) e2 hsl31'
    rw [show s + 31 + 1 = s + 32 by omega] at f1 f2
    have hwf32 := (row_shape hL (r := s + 32) (by omega)).1
    have hpw32 := (hwf32 f1).2
    obtain ⟨g1, g2, g3⟩ := winEnd hL hH hsg hwle (by omega) (by omega) hpw32
    have run2 := winRun hL hH hsg (show s ≤ s + 32 by omega) hpw32
    have hlf63 : tr.cell tt (s + 32 + 31) lf = tr.cell tt s lf := by
      rw [show s + 32 + 31 = s + 63 by omega]; exact (hrows 63 (by omega)).2.2.2.2 lf (by simp [segConst])
    have hwn63 : tr.cell tt (s + 32 + 31) wn = 1 := by rw [(run2 31 (by omega) g3).2.1, f2]
    have hsl63 := (row_shape hL (r := s + 32 + 31) (by omega)).2.2.2
    have hsl63' : tr.cell tt (s + 32 + 31) sl = 1 := by rw [hsl63, g2, hwn63, hlf63, hl0]; grind
    have h64 : ℓ = 64 := by
      rcases Nat.lt_or_ge 64 ℓ with h | h
      · have := (hrows 63 (by omega)).2.2.1 (by omega)
        rw [show s + 63 = s + 32 + 31 by omega, hsl63'] at this; exact absurd this (by decide)
      · omega
    subst h64
    refine ⟨Or.inr ⟨hl0, rfl⟩, fun o ho => ?_⟩
    by_cases ho1 : o < 32
    · exact w1 o ho1 ho
    · obtain ⟨r1, r2, r3, r4⟩ := run2 (o - 32) (by omega) (fun d' h => g3 d' (by omega))
      rw [show s + 32 + (o - 32) = s + o by omega] at r1 r2 r3 r4
      rw [if_neg ho1, r2, f2, show o % 32 = o - 32 by omega, r1, show s + o - (o - 32) = s + 32 by omega]
      refine ⟨rfl, rfl, ?_, r4⟩
      by_cases h0 : o = 32
      · subst h0; simpa using f1
      · rw [if_neg (by omega)]; exact r3 (by omega)
  · -- leaf segment: one window
    have hsl31' : tr.cell tt (s + 31) sl = 1 := by rw [hsl31, e2, hwn31, hlf31, hl1]; grind
    have h32 : ℓ = 32 := by
      rcases Nat.lt_or_ge 32 ℓ with h | h
      · have := (hrows 31 (by omega)).2.2.1 (by omega)
        rw [hsl31'] at this; exact absurd this (by decide)
      · omega
    subst h32
    exact ⟨Or.inl ⟨hl1, rfl⟩, fun o ho => w1 o ho ho⟩

end

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
