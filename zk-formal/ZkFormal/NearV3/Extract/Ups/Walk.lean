import ZkFormal.NearV3.Extract.Ups.WalkRows
import ZkFormal.NearV3.Extract.Ups.Plan
import ZkFormal.NearV3.Extract.WalkView

/-!
# ZkFormal.NearV3.Extract.Ups.Walk — `W0 … W3` as a `walkV3` walk (layer 2)

`upsWalk s : WalkR`: the four walk rows as `WStep3`s (mode `0` step / `1` absent by key /
`2` absent at a branch / `3` drain, symbols `START 0 15 END`, the edge message, the `BMAP`
message; one use-count column `u` for both).  `ups_walk`: it satisfies `WalkWf3` (so the
`walkV3` link `walk3_find` applies to it, with the key `[0, 15]`), provided the `BMAP` bitmap of
an absent-at-`END` row `W3` is a 16-bit value (`hbm`; in the link it comes from `BMAP`
balance with `nodeV3`, whose bitmaps are 16-bit).  `ups_walkTerm`: the terminal row
`t* = si + 1` and the case selector, levels and path records.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Walk row `i` as a `walkV3` step. -/
def stepOf (C : URow) (i : Nat) : WStep3 :=
  { mode := if C mS = 1 then 0 else if C mK = 1 then 1 else if C mB = 1 then 2 else 3,
    sym := wsym i, e := [C nN, C nI, C nib, C nN2, C nI2, C ek], u := C u, bm := C wbm, hv := C hv, ub := C u }

/-- The walk of a segment (`w` is not used by `upsV3`: no `FINAL`). -/
def upsWalk (s : UpsSeg) : WalkR := ⟨0, s.row 0 tau, (List.range 4).map fun i => stepOf (s.row i) i⟩

theorem upsWalk_len (s : UpsSeg) : (upsWalk s).steps.length = 4 := by simp [upsWalk]

theorem upsWalk_step (s : UpsSeg) {i : Nat} (hi : i < 4) : (upsWalk s).step i = stepOf (s.row i) i := by
  simp [WalkR.step, upsWalk, List.getD_eq_getElem?_getD, hi]

theorem upsWalk_syms (s : UpsSeg) : (upsWalk s).steps.map (·.sym) = [SYM_START, 0, 15, SYM_END] := by
  simp [upsWalk, stepOf, wsym, List.range_succ]

theorem mode_cases {C : URow} (h : C mS ≤ 1 ∧ C mK ≤ 1 ∧ C mB ≤ 1 ∧ C mS + C mK + C mB ≤ 1 ∧ C hv ≤ 1) (i : Nat) :
    ((stepOf C i).mode = 0 ↔ C mS = 1) ∧ ((stepOf C i).mode = 1 ↔ C mK = 1) ∧
    ((stepOf C i).mode = 2 ↔ C mB = 1) ∧ ((stepOf C i).mode = 3 ↔ C mS + C mK + C mB = 0) ∧
    (stepOf C i).mode ≤ 3 := by
  obtain ⟨a, b, c', d, -⟩ := h
  simp only [stepOf]
  by_cases h1 : C mS = 1
  · simp [h1] <;> omega
  · by_cases h2 : C mK = 1
    · simp [h1, h2] <;> omega
    · by_cases h3 : C mB = 1
      · simp [h1, h2, h3] <;> omega
      · simp [h1, h2, h3] <;> omega

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
  {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw hs hL

theorem wRowK (i : Nat) (hi : i < 4) : WRowK (s.row i) i := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  obtain ⟨-, -, hwk, bsf, bw1, bw2, bw3, -, -, bwk, -⟩ := kinds (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)
  obtain ⟨-, h0, h1, h2, h3⟩ := hL.walk
  have wk1 := hL.wk i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    exact ⟨hi, by simp; omega, by simp; omega, by simp; omega, by simp; omega, wk1⟩

theorem wRowF (i : Nat) (hi : i < 4) : WalkRowF (s.row i) (s.next i) i := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  have hn : i + 1 < s.rows.length := by have := hL.walk.1; omega
  have bD := fun {x} (hx : x ∈ rowBools) => le1 (rowBool (okRow hw hs hn) (rowLt hw hs _) hx)
  simp only [← next_eq hw hs hn] at bD
  exact walkRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (wRowK hw hs hL i hi)
    ⟨bD (by decide), bD (by decide), bD (by decide)⟩

/-- **`W0 … W3` form a `walkV3` walk.** -/
theorem ups_walk (hbm : s.row 3 mB = 1 → s.row 3 wbm < 2 ^ 16) :
    WalkWf3 [upsWalk s] ∧ (upsWalk s).steps.map (·.sym) = [SYM_START, 0, 15, SYM_END] ∧
      (upsWalk s).tau = s.row 0 tau := by
  have F := fun i (hi : i < 4) => wRowF hw hs hL i hi
  have Mc := fun i (hi : i < 4) => mode_cases (F i hi).modes i
  have hP := P_big
  refine ⟨⟨fun wv hwv => ?_, fun wv hwv => ?_, fun wv hwv i hi => ?_, fun wv hwv => ?_, fun wv hwv i hi => ?_, ?_⟩,
    upsWalk_syms s, rfl⟩
  all_goals try (simp only [List.mem_singleton] at hwv; subst hwv)
  · rw [upsWalk_len]; omega
  · refine ⟨by simp only [upsWalk]; unfold P; omega, rowLt hw hs _ _, fun st hst => ?_⟩
    simp only [upsWalk, List.mem_map, List.mem_range] at hst
    obtain ⟨j, hj, rfl⟩ := hst
    refine ⟨by simp only [stepOf, wsym]; rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [SYM_START, SYM_END] <;> unfold P <;> omega, rowLt hw hs _ _, rowLt hw hs _ _, fun x hx => ?_⟩
    simp only [stepOf, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact rowLt hw hs _ _
  · have hi4 : i < 4 := by rw [upsWalk_len] at hi; exact hi
    simp only [upsWalk, List.getElem_map, List.getElem_range]
    have Fi := F i hi4
    have Mi := Mc i hi4
    have hlast : (i + 1 == ((List.range 4).map fun i => stepOf (s.row i) i).length) = (i == 3) := by simp <;> omega
    rw [hlast]
    refine ⟨Mi.2.2.2.2, by simp [stepOf], fun hm => ?_, fun hm => ?_, fun hm => ?_, fun hl => ?_⟩
    · have := Fi.stepE (Mi.1.1 hm)
      refine ⟨by simp [stepOf]; exact this.1, fun hl => ?_, fun hl => ?_⟩
      · simp at hl; simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero]; exact this.2.1 (by omega)
      · simp at hl; simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero]; exact this.2.2 hl
    · have := Fi.absK (Mi.2.1.1 hm)
      refine ⟨by simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero]; exact this.1, ?_⟩
      simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero]; exact this.2
    · have hB := Mi.2.2.1.1 hm
      have := Fi.absB hB
      have hhv := Fi.modes.2.2.2.2
      refine ⟨by simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero]; exact this.1, ?_, hhv,
        fun hl => by simp at hl; subst hl; exact this.2.1 rfl, fun hl => ?_⟩
      · simp only [stepOf]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
        · exact absurd (Fi.start rfl).1 (by have := Fi.modes; omega)
        · exact (this.2.2 (Or.inl rfl)).1
        · exact (this.2.2 (Or.inr rfl)).1
        · exact hbm hB
      · simp at hl
        simp only [stepOf]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · exact absurd (Fi.start rfl).1 (by have := Fi.modes; omega)
        · exact ⟨by simp [wsym], (this.2.2 (Or.inl rfl)).2⟩
        · exact ⟨by simp [wsym], (this.2.2 (Or.inr rfl)).2⟩
    · simp at hl; subst hl; simp [stepOf, wsym]
  · rw [upsWalk_step s (by omega)]
    have := (F 0 (by omega)).start rfl
    exact ⟨by simp [stepOf, this.1], by simp [stepOf, wsym], by simp [stepOf, upsWalk, this.2.2.1]⟩
  · rw [upsWalk_len] at hi
    rw [upsWalk_step s (by omega), upsWalk_step s (by omega)]
    have Fi := F i (by omega)
    have Mi := Mc i (by omega)
    have Mn := Mc (i + 1) hi
    have hn : i + 1 < s.rows.length := by have := hL.walk.1; omega
    have nx := next_eq hw hs hn
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have := Fi.stepN (by omega) (Mi.1.1 hm)
      rw [nx] at this
      refine ⟨by simp [stepOf, this.1, this.2.1], fun h3 => ?_⟩
      have := Mn.2.2.2.1.1 h3; omega
    · have h0 : s.row i mS = 0 := by
        have := Fi.modes.1
        rcases (show s.row i mS = 0 ∨ s.row i mS = 1 by omega) with h | h
        · exact h
        · exact absurd (Mi.1.2 h) hm
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · exact absurd ((F 0 (by omega)).start rfl).1 (by omega)
      · have := Fi.drainN (Or.inl rfl) h0
        rw [nx] at this; exact Mn.2.2.2.1.2 this
      · have := Fi.drainN (Or.inr rfl) h0
        rw [nx] at this; exact Mn.2.2.2.1.2 this
  · simp [upsWalk]

/-- **The terminal row and the case selector** (`t* = si + 1`): the rows before `t*` are steps;
at `t*` the mode is the case's (`LP`/`BR` step, `BV`/`BI` absent at a branch, splits absent by
key, `LSa` by a `LEND` edge), the position is `I = ti`, the level `D = di`, and an absent-by-key
terminal other than `LSa` has the record nibble `x = tX`; a step terminal is `W3`.  `W3` sends
`S0F (τ, mS, mS·N2)`. -/
theorem ups_walkTerm {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx) :
    (∀ i, 1 ≤ i → i ≤ si → s.row i mS = 1) ∧
    s.row (si + 1) mS = (if ci ≤ 1 then 1 else 0) ∧ s.row (si + 1) mB = (if ci = 2 ∨ ci = 3 then 1 else 0) ∧
    s.row (si + 1) mK = (if 4 ≤ ci then 1 else 0) ∧
    (ci ≤ 1 → si = 2) ∧
    s.row (si + 1) nI = ti ∧ s.row (si + 1) lv0 = (if di = 0 then 1 else 0) ∧
    s.row (si + 1) lv1 = (if di = 1 then 1 else 0) ∧ s.row (si + 1) lv2 = (if di = 2 then 1 else 0) ∧
    (4 ≤ ci → (ci = 4 → s.row (si + 1) ek = EK_LEND) ∧
      (ci ≠ 4 → s.row (si + 1) ek = EK_KEY ∧ s.row (si + 1) nib = s.row (si + 1) tX)) ∧
    s.row 3 pres = s.row 3 mS ∧ s.row 3 vid = s.row 3 mS * s.row 3 nN2 := by
  obtain ⟨i1, i2, i3, i4⟩ := hP.ix
  have T := fun i (h1 : 1 ≤ i) (h4 : i < 4) => by
    have hlt : i < s.rows.length := by have := hL.walk.1; omega
    obtain ⟨c1, c2, c3, c4⟩ := hP.seg i hlt
    exact walkTerm (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (wRowK hw hs hL i h4) h1 i1 i2 i3 i4 c1 c2 c3 c4
  have Tt := T (si + 1) (by omega) (by omega)
  have Tm := Tt.2.2.2.2.2.1 rfl
  have Td := Tt.2.2.2.2.1 rfl
  refine ⟨fun i h1 h2 => ?_, Tm.1, Tm.2.1, Tm.2.2, fun h => ?_, Td.1, Td.2.1, Td.2.2.1, Td.2.2.2,
    fun h => Tt.2.2.2.2.2.2.1 rfl (by rw [Tm.2.2, if_pos h]), (T 3 (by omega) (by omega)).2.2.2.2.2.2.2 rfl |>.1,
    (T 3 (by omega) (by omega)).2.2.2.2.2.2.2 rfl |>.2⟩
  · rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
    · exact (T 1 (by omega) (by omega)).2.1 rfl (by omega)
    · exact (T 2 (by omega) (by omega)).2.2.1 rfl (by omega)
  · have := Tt.2.2.2.1 rfl (by rw [Tm.1, if_pos h]); omega

/-- **Levels and path records**: `W1` is at level 0; a step of `W1`/`W2` enters a new record
iff `enter` (then it lands on position 0, else it stays in the record), advancing the level;
every lookup row's record is the path record `N_lv` of its level. -/
theorem ups_walkLev :
    s.row 1 lv0 = 1 ∧ s.row 1 lv1 = 0 ∧ s.row 1 lv2 = 0 ∧
    (∀ i, (i = 1 ∨ i = 2) → s.row i mS = 1 → s.row i enter ≤ 1 ∧
      (s.row i enter = 1 → s.row i nI2 = 0) ∧ (s.row i enter = 0 → s.row i nN2 = s.row i nN) ∧
      (s.row (i + 1) lv0 + s.row i lv0 * s.row i enter) % P = s.row i lv0 ∧
      (s.row (i + 1) lv1 + s.row i lv1 * s.row i enter) % P = (s.row i lv1 + s.row i lv0 * s.row i enter) % P ∧
      (s.row (i + 1) lv2 + s.row i lv2 * s.row i enter) % P = (s.row i lv2 + s.row i lv1 * s.row i enter) % P) ∧
    (∀ i, 1 ≤ i → i < 4 → s.row i mS + s.row i mK + s.row i mB = 1 →
      s.row i lv0 + s.row i lv1 + s.row i lv2 = 1 →
      s.row i nN = s.row i lv0 * s.row i N0 + s.row i lv1 * s.row i N1 + s.row i lv2 * s.row i N2) := by
  have Lv := fun i (h1 : 1 ≤ i) (h4 : i < 4) => by
    have hlt : i < s.rows.length := by have := hL.walk.1; omega
    exact walkLev (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _) (wRowK hw hs hL i h4) h1
  have L1 := (Lv 1 (by omega) (by omega)).2.2.2.2.1 rfl
  refine ⟨L1.1, L1.2.1, L1.2.2, fun i hi hm => ?_, fun i h1 h4 hm hl => (Lv i h1 h4).2.2.2.2.2.2 hm hl⟩
  have hn : i + 1 < s.rows.length := by have := hL.walk.1; omega
  have := (Lv i (by omega) (by omega))
  have h := this.2.2.2.2.2.1 hi hm
  rw [next_eq hw hs hn] at h
  exact ⟨this.2.2.2.1, h⟩

end

end ZkFormal.NearV3.UpsRows
