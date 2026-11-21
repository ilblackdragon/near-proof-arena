import M5T1.MsgRow

/-!
# M5T1.MsgRowSpan — `MSG` rows form messages; message ids (F-2)

* `span_of`: every active row of `MSG` lies in a message span (`IsSpan`): the last `first` row at or
  before it, the first `endm` row at or after it (row `0` starts a message; no active row after a
  padding row; the last row of an active run ends a message);
* `span_end_unique`: a span's end is determined by its start;
* `j_span`, `mId_span`: within a span, `j` counts the bytes and the message id `128·mf + 96 + mt`
  is constant;
* **`span_start_unique`**: under `MIdBound` (every active row's message id is `< 2^30`), two spans
  with the same message id are the same span. The `dm` constraint makes the ids of consecutive
  messages increase by `1 + dm` with `dm < 2^24` **modulo `p`**; without a bound the ids can wrap
  around `p` after about `p / 2^24 ≈ 120` messages and repeat (see the report in `MsgRowDg.lean`).
-/

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus

/-- The message id of `MSG` row `r` (as a natural `< p`). -/
def MI (tr : Trace Fp) (pub : List Fp) (r : Nat) : Nat := ev tr 3 r pub Msg.mId

/-- **Premise**: every active `MSG` row's message id is below `2^30` (e.g. every family `mf` is
below `2^23 − 1`): ids do not wrap around `p`. -/
def MIdBound (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r < tr.height 3, V tr pub r "act" = 1 → MI tr pub r < 2 ^ 30

theorem MI_eq {tr : Trace Fp} {pub : List Fp} (r : Nat) :
    MI tr pub r = (128 * V tr pub r "mf" + 96 + V tr pub r "mt") % 2013265921 := by
  unfold MI Msg.mId
  simp only [ev_hadd, ev_hmul, ev_K', evc]
  have := V_lt tr pub r "mf"; have := V_lt tr pub r "mt"
  omega

/-- A least element above `x` of a (classically decidable) property. -/
theorem exists_least (P : Nat → Prop) (x : Nat) :
    ∀ n z, z ≤ x + n → x ≤ z → P z → ∃ m, x ≤ m ∧ m ≤ z ∧ P m ∧ ∀ w, x ≤ w → w < m → ¬ P w := by
  intro n
  induction n with
  | zero => intro z h1 h2 hp; exact ⟨z, h2, Nat.le_refl _, hp, fun w h1' h2' => by omega⟩
  | succ n ih =>
    intro z h1 h2 hp
    by_cases hw : ∃ w, x ≤ w ∧ w < z ∧ P w
    · obtain ⟨w, hw1, hw2, hw3⟩ := hw
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := ih w (by omega) hw1 hw3
      exact ⟨m, hm1, by omega, hm3, hm4⟩
    · exact ⟨z, h2, Nat.le_refl _, hp, fun w h1' h2' hp' => hw ⟨w, h1', h2', hp'⟩⟩

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}
variable (H : Holds (fullAir tape xtape) pub tr)
include H

/-- `(1 − act)·endm`: an `endm` row is active. -/
theorem c7 {r : Nat} (hr : r < tr.height 3) (hm : V tr pub r "endm" = 1) : V tr pub r "act" = 1 := by
  have h := mc H hr 7 (by decide) ((1 - Msg.c "act") * Msg.c "endm") rfl
  simp only [ev_hsub, ev_hmul, ev_one', evc, hm] at h
  have := V_lt tr pub r "act"; omega

/-- The `dm` constraint: the next message's id is `mId + 1 + dm` (mod `p`). -/
theorem c34 {r : Nat} (hr : r + 1 < tr.height 3) (hA : V tr pub (r + 1) "act" = 1)
    (hf : V tr pub (r + 1) "first" = 1) (h0 : V tr pub r "dm" 0 < 256) (h1 : V tr pub r "dm" 1 < 256)
    (h2 : V tr pub r "dm" 2 < 256) :
    MI tr pub (r + 1) = (MI tr pub r + 1 + (V tr pub r "dm" 0 + 256 * V tr pub r "dm" 1 +
      65536 * V tr pub r "dm" 2)) % 2013265921 := by
  have h := mc H (r := r) (by omega) 34 (by decide)
    (.mul (.isTransition * Msg.n "act" * Msg.n "first")
      (Msg.mIdN - Msg.mId - 1 - (Msg.c "dm" 0 + K 256 * Msg.c "dm" 1 + K 65536 * Msg.c "dm" 2))) rfl
  have hN : ev tr 3 r pub Msg.mIdN = MI tr pub (r + 1) := by
    unfold MI; simp only [Msg.mIdN, Msg.mId, ev_hadd, ev_hmul, ev_K', evc, evn hr]
  have hD : ev tr 3 r pub (Msg.c "dm" 0 + K 256 * Msg.c "dm" 1 + K 65536 * Msg.c "dm" 2) =
      V tr pub r "dm" 0 + 256 * V tr pub r "dm" 1 + 65536 * V tr pub r "dm" 2 := by
    simp only [ev_hadd, ev_hmul, ev_K', evc, Nat.reduceMod]; omega
  have hG : ev tr 3 r pub (.isTransition * Msg.n "act" * Msg.n "first") = 1 := by
    simp only [ev_hmul, evn hr, ev_tr hr, hA, hf]
  rw [ev_mul, hG, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _), ev_hsub, ev_hsub, ev_hsub, hN, hD, ev_one'] at h
  have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) Msg.mId
  have := ev_lt (tr := tr) (t := 3) (r := r + 1) (pub := pub) Msg.mId
  unfold MI at *
  omega

/-- A padding row is followed by padding rows only. -/
theorem pad_after {w : Nat} (hw : w < tr.height 3) (hA : V tr pub w "act" = 0) :
    ∀ d, w + d < tr.height 3 → V tr pub (w + d) "act" = 0 := by
  intro d
  induction d with
  | zero => intro _; exact hA
  | succ d ih => intro hd; exact c10 H (r := w + d) (by omega) (ih (by omega))

theorem act_le {r : Nat} (hr : r < tr.height 3) (RH : RowHyps tr pub) : V tr pub r "act" ≤ 1 := by
  obtain ⟨g, -, hd⟩ := RH.desc r hr
  rw [hd.act]; exact b2n_le _

/-- An active row at or after `y` with no `first` in `(y, x]`, and `first` at `y`: no `endm` in
`[y, x)`. -/
theorem no_endm_before (RH : RowHyps tr pub) {y x : Nat} (hx : x < tr.height 3) (hyx : y ≤ x)
    (hA : V tr pub x "act" = 1) (hnf : ∀ z, y < z → z ≤ x → V tr pub z "first" = 0) :
    ∀ w, y ≤ w → w < x → V tr pub w "endm" = 0 := by
  intro w h1 h2
  have hm := endm_le H (r := w) (by omega)
  rcases (show V tr pub w "endm" = 0 ∨ V tr pub w "endm" = 1 by omega) with h | h
  · exact h
  · exfalso
    have he := c45 H (by omega) h
    have hf := c11 H (r := w) (by omega) (e_le H (by omega)) (endm_le H (by omega))
    rw [he, h] at hf
    simp only [and_self, ite_true] at hf
    have hal := act_le H (r := w + 1) (by omega) RH
    rcases (show V tr pub (w + 1) "act" = 0 ∨ V tr pub (w + 1) "act" = 1 by omega) with h0 | h1
    · have := pad_after H (w := w + 1) (by omega) h0 (x - (w + 1)) (by omega)
      rw [show w + 1 + (x - (w + 1)) = x by omega, hA] at this
      exact absurd this (by decide)
    · have := hnf (w + 1) (by omega) (by omega)
      rw [hf, h1] at this; exact absurd this (by decide)

/-- The last `first` row at or before `x`. -/
theorem last_first {x : Nat} (hx : x < tr.height 3) :
    ∃ y, y ≤ x ∧ V tr pub y "first" = 1 ∧ ∀ z, y < z → z ≤ x → V tr pub z "first" = 0 := by
  induction x with
  | zero => exact ⟨0, Nat.le_refl _, c9 H hx, fun z h1 h2 => by omega⟩
  | succ x ih =>
    have hf := first_le H hx
    rcases (show V tr pub (x + 1) "first" = 0 ∨ V tr pub (x + 1) "first" = 1 by omega) with h | h
    · obtain ⟨y, h1, h2, h3⟩ := ih (by omega)
      refine ⟨y, by omega, h2, fun z hz1 hz2 => ?_⟩
      by_cases hz : z = x + 1
      · rw [hz]; exact h
      · exact h3 z hz1 (by omega)
    · exact ⟨x + 1, Nat.le_refl _, h, fun z h1 h2 => by omega⟩

/-- An active row is followed (at or after it) by an `endm` row. -/
theorem some_endm {x : Nat} (hx : x < tr.height 3) (hA : V tr pub x "act" = 1) :
    ∃ z, x ≤ z ∧ z < tr.height 3 ∧ V tr pub z "endm" = 1 := by
  by_cases h : ∃ z, x ≤ z ∧ z < tr.height 3 ∧ V tr pub z "endm" = 1
  · exact h
  · exfalso
    have hall : ∀ d, x + d < tr.height 3 → V tr pub (x + d) "act" = 1 := by
      intro d
      induction d with
      | zero => intro _; exact hA
      | succ d ih =>
        intro hd
        have hm := endm_le H (r := x + d) (by omega)
        have h0 : V tr pub (x + d) "endm" = 0 := by
          rcases (show V tr pub (x + d) "endm" = 0 ∨ V tr pub (x + d) "endm" = 1 by omega) with h' | h'
          · exact h'
          · exact absurd ⟨x + d, by omega, by omega, h'⟩ h
        exact c12 H (r := x + d) (by omega) (ih (by omega)) h0
    have hl := hall (tr.height 3 - 1 - x) (by omega)
    rw [show x + (tr.height 3 - 1 - x) = tr.height 3 - 1 by omega] at hl
    have := c49 H (r := tr.height 3 - 1) (by omega) hl
    exact h ⟨tr.height 3 - 1, by omega, by omega, this⟩

/-- **Every active row lies in a message span.** -/
theorem span_of (RH : RowHyps tr pub) {x : Nat} (hx : x < tr.height 3) (hA : V tr pub x "act" = 1) :
    ∃ r0 r1, IsSpan tr pub r0 r1 ∧ r0 ≤ x ∧ x ≤ r1 := by
  obtain ⟨y, hy1, hy2, hy3⟩ := last_first H hx
  obtain ⟨z, hz1, hz2, hz3⟩ := some_endm H hx hA
  obtain ⟨m, hm1, hm2, hm3, hm4⟩ := exists_least (fun w => V tr pub w "endm" = 1) x (z - x) z (by omega) hz1 hz3
  have hne := no_endm_before H RH hx hy1 hA hy3
  refine ⟨y, m, ⟨by omega, by omega, hy2, hm3, fun w h1 h2 => ?_⟩, hy1, hm1⟩
  by_cases hw : w < x
  · exact hne w h1 hw
  · have := endm_le H (r := w) (by omega)
    rcases (show V tr pub w "endm" = 0 ∨ V tr pub w "endm" = 1 by omega) with h | h
    · exact h
    · exact absurd h (hm4 w (by omega) h2)

theorem span_end_unique {r0 r1 r1' : Nat} (h : IsSpan tr pub r0 r1) (h' : IsSpan tr pub r0 r1') : r1 = r1' := by
  by_cases hlt : r1 < r1'
  · have := h'.mid r1 h.le hlt; rw [h.endm] at this; exact absurd this (by decide)
  · by_cases hgt : r1' < r1
    · have := h.mid r1' h'.le hgt; rw [h'.endm] at this; exact absurd this (by decide)
    · omega

theorem j_span {r0 r1 : Nat} (hsp : IsSpan tr pub r0 r1) :
    ∀ d, r0 + d ≤ r1 → V tr pub (r0 + d) "j" = d := by
  have hHt := msg_height H
  have hl := hsp.lt
  intro d
  induction d with
  | zero => intro _; exact (cfirst H (by omega) hsp.first).1
  | succ d ih =>
    intro hd
    rw [← Nat.add_assoc, c18 H (r := r0 + d) (by omega) (inm_span H hsp (by omega) (by omega)), ih (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

theorem mId_span {r0 r1 : Nat} (hsp : IsSpan tr pub r0 r1) :
    ∀ d, r0 + d ≤ r1 → MI tr pub (r0 + d) = MI tr pub r0 := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hi := inm_span H hsp (x := r0 + d) (by omega) (by omega)
    have hl := hsp.lt
    rw [← ih (by omega), ← Nat.add_assoc, MI_eq, MI_eq, c14 H (by omega) hi, c15 H (by omega) hi]

theorem mId_span' {r0 r1 x : Nat} (hsp : IsSpan tr pub r0 r1) (h1 : r0 ≤ x) (h2 : x ≤ r1) :
    MI tr pub x = MI tr pub r0 := by
  have := mId_span H hsp (x - r0) (by omega); rwa [Nat.add_sub_cancel' h1] at this

/-- Message ids increase along the table (under `MIdBound`). -/
theorem mId_mono (hB : MIdBound tr pub) (RH : RowHyps tr pub) (hr1 : NoRng tape) (hr2 : NoRng xtape)
    {a : Nat} (ha : a < tr.height 3) :
    ∀ d, a + d < tr.height 3 → V tr pub (a + d) "act" = 1 →
      MI tr pub a ≤ MI tr pub (a + d) ∧
      ((∃ y, a < y ∧ y ≤ a + d ∧ V tr pub y "first" = 1) → MI tr pub a < MI tr pub (a + d)) := by
  intro d
  induction d with
  | zero => intro _ _; exact ⟨Nat.le_refl _, fun ⟨y, h1, h2, _⟩ => by omega⟩
  | succ d ih =>
    intro hd hA
    rw [← Nat.add_assoc] at hA ⊢
    have hA0 : V tr pub (a + d) "act" = 1 := by
      have := act_le H (r := a + d) (by omega) RH
      rcases (show V tr pub (a + d) "act" = 0 ∨ V tr pub (a + d) "act" = 1 by omega) with h | h
      · have := c10 H (r := a + d) (by omega) h; rw [hA] at this; exact absurd this (by decide)
      · exact h
    obtain ⟨ih1, ih2⟩ := ih (by omega) hA0
    have hf := first_le H (r := a + d + 1) (by omega)
    rcases (show V tr pub (a + d + 1) "first" = 0 ∨ V tr pub (a + d + 1) "first" = 1 by omega) with h | h
    · have hi := c13 H (r := a + d) (by omega) hA h
      have heq : MI tr pub (a + d + 1) = MI tr pub (a + d) := by
        rw [MI_eq, MI_eq, c14 H (by omega) hi, c15 H (by omega) hi]
      rw [heq]
      refine ⟨ih1, fun ⟨y, h1, h2, h3⟩ => ih2 ⟨y, h1, ?_, h3⟩⟩
      by_cases hy : y = a + d + 1
      · rw [hy, h] at h3; exact absurd h3 (by decide)
      · omega
    · have hb0 := hB (a + d) (by omega) hA0
      have h0 := dm_lt H hr1 hr2 (r := a + d) (by omega) hA0 0 (by decide)
      have h1 := dm_lt H hr1 hr2 (r := a + d) (by omega) hA0 1 (by decide)
      have h2 := dm_lt H hr1 hr2 (r := a + d) (by omega) hA0 2 (by decide)
      have hm := c34 H (r := a + d) (by omega) hA h h0 h1 h2
      rw [Nat.mod_eq_of_lt (by omega)] at hm
      exact ⟨by omega, fun _ => by omega⟩

/-- **Two spans with the same message id are the same span** (under `MIdBound`). -/
theorem span_start_unique (hB : MIdBound tr pub) (RH : RowHyps tr pub) (hr1 : NoRng tape)
    (hr2 : NoRng xtape) {a0 a1 b0 b1 : Nat} (ha : IsSpan tr pub a0 a1) (hb : IsSpan tr pub b0 b1)
    (he : MI tr pub a0 = MI tr pub b0) : a0 = b0 ∧ a1 = b1 := by
  have key : ∀ {a0 a1 b0 b1 : Nat}, IsSpan tr pub a0 a1 → IsSpan tr pub b0 b1 → a0 < b0 →
      MI tr pub a0 < MI tr pub b0 := by
    intro a0 a1 b0 b1 ha hb hlt
    have hbl := hb.lt; have hbe := hb.le
    have := (mId_mono H hB RH hr1 hr2 (a := a0) (by omega) (b0 - a0) (by omega)
      (by rw [Nat.add_sub_cancel' (by omega)]; exact c6 H (by omega) hb.first)).2
      ⟨b0, hlt, by omega, hb.first⟩
    rwa [Nat.add_sub_cancel' (by omega)] at this
  have h0 : a0 = b0 := by
    by_cases h1 : a0 < b0
    · have := key ha hb h1; omega
    · by_cases h2 : b0 < a0
      · have := key hb ha h2; omega
      · omega
  subst h0
  exact ⟨rfl, span_end_unique H ha hb⟩
end

#print axioms span_of
#print axioms span_start_unique

end M5T1.MsgRow
