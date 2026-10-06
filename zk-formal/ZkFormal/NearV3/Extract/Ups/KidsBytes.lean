import ZkFormal.NearV3.Extract.Ups.RbrBytes

/-!
# ZkFormal.NearV3.Extract.Ups.KidsBytes — child slots and window flags (layer 2)

Spec side: `kidAt cs n` (slot `n`), `kidsLen cs` (the number of slots); setting an occupied
slot `0` / the last slot replaces the first / last child hash and keeps the bitmap
(`setKid_first`, `setKid_last`, `bitmap_setKid`); setting an empty slot `0` / the last slot
prepends / appends the hash and adds the slot's bit (`setKid_first_ins`, `setKid_last_ins`,
`bitmap_setKid_ins`).

Row side: in a branch part with `w` windows at `o + c0`, the window flags are `fw = [e = 0]` and
`lastw = [e = w − 1]` on every row of window `e` (`winFlags`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsSpec

open NearSpec

/-- Slot `n` of a child list. -/
def kidAt : Kids → Nat → Option PTrie
  | .nil, _ => none
  | .none _, 0 => none
  | .some c _, 0 => some c
  | .none r, n + 1 => kidAt r n
  | .some _ r, n + 1 => kidAt r n

/-- The number of slots. -/
def kidsLen : Kids → Nat
  | .nil => 0
  | .none r => kidsLen r + 1
  | .some _ r => kidsLen r + 1

theorem setKid_first (cs : Kids) (c c' : PTrie) (h : kidAt cs 0 = some c) :
    ∃ R, Kids.hashes cs = c.hashOf ++ R ∧ Kids.hashes (setKid cs 0 c') = c'.hashOf ++ R := by
  cases cs with
  | nil => simp [kidAt] at h
  | none r => simp [kidAt] at h
  | some d r => simp [kidAt] at h; subst h; exact ⟨Kids.hashes r, by simp [Kids.hashes], by simp [setKid, Kids.hashes]⟩

theorem setKid_last (c c' : PTrie) : ∀ (cs : Kids) (n : Nat), kidsLen cs = n + 1 → kidAt cs n = some c →
    ∃ R, Kids.hashes cs = R ++ c.hashOf ∧ Kids.hashes (setKid cs n c') = R ++ c'.hashOf
  | .nil, _, h, _ => by simp [kidsLen] at h
  | .none r, 0, _, h => by simp [kidAt] at h
  | .none r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    obtain ⟨R, h1, h2⟩ := setKid_last c c' r n (by omega) h
    exact ⟨R, by simpa [Kids.hashes] using h1, by simpa [setKid, Kids.hashes] using h2⟩
  | .some d r, 0, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    cases r with
    | nil => simp at h; subst h; exact ⟨[], by simp [Kids.hashes], by simp [setKid, Kids.hashes]⟩
    | none r => simp [kidsLen] at hl
    | some _ r => simp [kidsLen] at hl
  | .some d r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    obtain ⟨R, h1, h2⟩ := setKid_last c c' r n (by omega) h
    exact ⟨d.hashOf ++ R, by simp [Kids.hashes, h1], by simp [setKid, Kids.hashes, h2]⟩

theorem bitmap_setKid (c c' : PTrie) : ∀ (cs : Kids) (n i : Nat), kidAt cs n = some c →
    kidsBitmap (setKid cs n c') i = kidsBitmap cs i
  | .nil, _, _, h => by simp [kidAt] at h
  | .none r, 0, _, h => by simp [kidAt] at h
  | .some d r, 0, i, _ => by simp [setKid, kidsBitmap]
  | .none r, n + 1, i, h => by
    simp only [kidAt] at h; simp [setKid, kidsBitmap, bitmap_setKid c c' r n (i + 1) h]
  | .some d r, n + 1, i, h => by
    simp only [kidAt] at h; simp [setKid, kidsBitmap, bitmap_setKid c c' r n (i + 1) h]

theorem setKid_first_ins (cs : Kids) (c' : PTrie) (h : kidAt cs 0 = none) (hl : 0 < kidsLen cs) :
    Kids.hashes (setKid cs 0 c') = c'.hashOf ++ Kids.hashes cs ∧
    ∀ i, kidsBitmap (setKid cs 0 c') i = 2 ^ i + kidsBitmap cs i := by
  cases cs with
  | nil => simp [kidsLen] at hl
  | none r => exact ⟨by simp [setKid, Kids.hashes], fun i => by simp [setKid, kidsBitmap]⟩
  | some d r => simp [kidAt] at h

theorem setKid_last_ins (c' : PTrie) : ∀ (cs : Kids) (n : Nat), kidsLen cs = n + 1 → kidAt cs n = none →
    Kids.hashes (setKid cs n c') = Kids.hashes cs ++ c'.hashOf ∧
    ∀ i, kidsBitmap (setKid cs n c') i = kidsBitmap cs i + 2 ^ (i + n)
  | .nil, _, h, _ => by simp [kidsLen] at h
  | .some d r, 0, _, h => by simp [kidAt] at h
  | .none r, 0, hl, _ => by
    simp only [kidsLen] at hl
    cases r with
    | nil => exact ⟨by simp [setKid, Kids.hashes], fun i => by simp [setKid, kidsBitmap]⟩
    | none r => simp [kidsLen] at hl
    | some _ r => simp [kidsLen] at hl
  | .none r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    obtain ⟨h1, h2⟩ := setKid_last_ins c' r n (by omega) h
    refine ⟨by simpa [setKid, Kids.hashes] using h1, fun i => ?_⟩
    simp only [setKid, kidsBitmap, h2 (i + 1)]
    congr 2; omega
  | .some d r, n + 1, hl, h => by
    simp only [kidsLen, kidAt] at hl h
    obtain ⟨h1, h2⟩ := setKid_last_ins c' r n (by omega) h
    refine ⟨by simp [setKid, Kids.hashes, h1], fun i => ?_⟩
    simp only [setKid, kidsBitmap, h2 (i + 1)]
    rw [show i + 1 + n = i + (n + 1) by omega]; omega

end ZkFormal.NearV3.UpsSpec

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **Window flags**: windows `e < w` at `r + 32e` (preceded by a non-window row, followed by
the `MEM` field): `fw = [e = 0]`, `lastw = [e = w − 1]`. -/
theorem winFlags {r w : Nat} (hw0 : 0 < w) (hlt : r + 32 * w < s.rows.length) (hr : 0 < r)
    (hprev : s.row (r - 1) sCH = 0)
    (W : ∀ e, e < w → UField s (r + 32 * e) 32 ∧ (∀ d, d < 32 → s.row (r + 32 * e + d) sCH = 1))
    (hmem : s.row (r + 32 * w) sMEM = 1) (hchM : s.row (r + 32 * w) sCH = 0) :
    ∀ e, e < w → ∀ d, d < 32 → s.row (r + 32 * e + d) fw = (if e = 0 then 1 else 0) ∧
      s.row (r + 32 * e + d) lastw = (if e + 1 = w then 1 else 0) := by
  have st := fun i (hi : i < s.rows.length) => winStep (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  have nx := fun i (hi : i + 1 < s.rows.length) => next_eq hw hs (i := i) hi
  have fe0 : ∀ e, e < w → ∀ d, d < 31 → s.row (r + 32 * e + d) fe = 0 := fun e he d hd => by
    rcases rowBool (okRow hw hs (i := r + 32 * e + d) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
    · exact h
    · have := ((W e he).1.fe d (by omega)).1 h; omega
  have fe1 : ∀ e, e < w → s.row (r + 32 * e + 31) fe = 1 := fun e he => ((W e he).1.fe 31 (by omega)).2 rfl
  -- the flags are constant inside a window
  have inW : ∀ e, e < w → ∀ d, d < 32 → s.row (r + 32 * e + d) fw = s.row (r + 32 * e) fw ∧
      s.row (r + 32 * e + d) lastw = s.row (r + 32 * e) lastw := by
    intro e he d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h := (st (r + 32 * e + d) (by omega)).2.1 ((W e he).2 d (by omega)) (fe0 e he d (by omega))
      rw [nx _ (by omega), show r + 32 * e + d + 1 = r + 32 * e + (d + 1) by omega] at h
      rw [h.1, h.2.1]; exact ih (by omega)
  -- first rows
  have first : ∀ e, e < w → s.row (r + 32 * e) fw = (if e = 0 then 1 else 0) := by
    intro e he
    rcases e with _ | e
    · have := (st (r - 1) (by omega)).1 hprev (by
        rw [nx _ (by omega), show r - 1 + 1 = r by omega]; simpa using (W 0 hw0).2 0 (by omega))
      rw [nx _ (by omega), show r - 1 + 1 = r by omega] at this
      simpa using this
    · have := (st (r + 32 * e + 31) (by omega)).2.2.1 ((W e (by omega)).2 31 (by omega)) (fe1 e (by omega))
        (by
          rw [nx _ (by omega)]
          have := (W (e + 1) he).2 0 (by omega); rwa [show r + 32 * (e + 1) + 0 = r + 32 * e + 31 + 1 by omega] at this)
      rw [nx _ (by omega), show r + 32 * e + 31 + 1 = r + 32 * (e + 1) by omega] at this
      simpa using this
  have last : ∀ e, e < w → s.row (r + 32 * e) lastw = (if e + 1 = w then 1 else 0) := by
    intro e he
    have := (st (r + 32 * e + 31) (by omega)).2.2.2 ((W e he).2 31 (by omega)) (fe1 e he)
    rw [nx _ (by omega)] at this
    rw [← (inW e he 31 (by omega)).2, this]
    split
    · next h => rw [show r + 32 * e + 31 + 1 = r + 32 * w by omega, hmem]
    · next h =>
      have := (W (e + 1) (by omega)).2 0 (by omega)
      rw [show r + 32 * (e + 1) + 0 = r + 32 * e + 31 + 1 by omega] at this
      have hoh := le1 (rowBool (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _) (x := sMEM)
        (by simp [rowBools, states]))
      have := stSum (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _)
      have := le1 (rowBool (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _) (x := qb)
        (by simp [rowBools]))
      omega
  intro e he d hd
  rw [(inW e he d hd).1, (inW e he d hd).2, first e he, last e he]
  exact ⟨rfl, rfl⟩

end

end ZkFormal.NearV3.UpsRows
