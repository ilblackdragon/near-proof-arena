import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsExt
import ZkFormal.NearV3.Extract.Ups.UpsPath
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {f : Nat → Nat} {vs : List NodeS3} {V : List ValRec3} {hds : List HeadE} {ws : List WalkR}
  {v : List UpsSeg} (G : Walk3.WalkHyp f vs V hds (allWalks ws v)) (hw : Wf v)
  {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)

omit G hw hL hP in
theorem upsWalk_mem (hs : s ∈ v) : upsWalk s ∈ allWalks ws v := List.mem_append_right _ (List.mem_map.2 ⟨s, hs, rfl⟩)

include hw hs hL in
theorem segN (i : Nat) (hi : i < 4) (d : Nat) (hd : d < 3) : s.row i (11 + d) = s.row 0 (11 + d) := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
  · exact hL.segc i hlt (11 + 0) (by decide)
  · exact hL.segc i hlt (11 + 1) (by decide)
  · exact hL.segc i hlt (11 + 2) (by decide)

include hw hs hL hP in
/-- **The walk's levels.** -/
theorem ups_levels : di ≤ si ∧ (1 ≤ di → 1 ≤ si ∧ s.row 1 mS = 1 ∧ s.row 1 nN = s.row 0 (11 + 0)) ∧
    (di = 2 → si = 2 ∧ s.row 2 mS = 1 ∧ s.row 2 nN = s.row 0 (11 + 1)) ∧
    s.row (si + 1) nN = s.row 0 (11 + di) := by
  obtain ⟨hstep, hT1, hT2, hT3, -, -, hl0, hl1, hl2, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨a0, a1, a2, hlev, hnN⟩ := ups_walkLev hw hs hL
  obtain ⟨-, -, i3, i4⟩ := hP.ix
  have F := fun i (hi : i < 4) => (wRowF hw hs hL i hi).modes
  have lt := fun i x => rowLt hw hs i x
  have hPl := P_lit
  have sN := segN hw hs hL
  -- the terminal row's record
  have hsumT : s.row (si + 1) mS + s.row (si + 1) mK + s.row (si + 1) mB = 1 := by
    rw [hT1, hT2, hT3]; split <;> split <;> split <;> omega
  have hlvT : s.row (si + 1) lv0 + s.row (si + 1) lv1 + s.row (si + 1) lv2 = 1 := by
    rw [hl0, hl1, hl2]; split <;> split <;> split <;> omega
  have hNT := hnN (si + 1) (by omega) (by omega) hsumT hlvT
  rw [show N0 = 11 + 0 from rfl, show N1 = 11 + 1 from rfl, show N2 = 11 + 2 from rfl] at hNT
  rw [hl0, hl1, hl2, sN (si + 1) (by omega) 0 (by omega), sN (si + 1) (by omega) 1 (by omega),
    sN (si + 1) (by omega) 2 (by omega)] at hNT
  have hNT' : s.row (si + 1) nN = s.row 0 (11 + di) := by
    rw [hNT]; rcases (show di = 0 ∨ di = 1 ∨ di = 2 by omega) with rfl | rfl | rfl <;> simp
  -- row 1
  have hN1 : 1 ≤ si → s.row 1 mS = 1 ∧ s.row 1 nN = s.row 0 (11 + 0) := by
    intro h1
    have hm := hstep 1 (by omega) h1
    have Fm := F 1 (by omega)
    have := hnN 1 (by omega) (by omega) (by omega) (by omega)
    rw [show N0 = 11 + 0 from rfl] at this
    rw [a0, a1, a2, sN 1 (by omega) 0 (by omega)] at this
    exact ⟨hm, by simpa using this⟩
  -- row 2's levels after a step on row 1
  have lev2 : 1 ≤ si → s.row 2 lv2 = 0 ∧ s.row 2 lv1 = s.row 1 enter ∧ s.row 1 enter ≤ 1 ∧
      s.row 2 lv0 + s.row 1 enter = 1 := by
    intro h1
    obtain ⟨he, -, -, r0, r1, r2⟩ := hlev 1 (Or.inl rfl) (hstep 1 (by omega) h1)
    simp only [a0, a1, a2, Nat.reduceAdd] at r0 r1 r2
    have := lt 2 lv0; have := lt 2 lv1; have := lt 2 lv2
    simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul, Nat.zero_add] at r0 r1 r2
    rw [hPl] at *
    refine ⟨by omega, by omega, he, by omega⟩
  refine ⟨?_, fun h => ?_, fun h => ?_, hNT'⟩
  · rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with rfl | rfl | rfl
    · have := hl0; rw [a0] at this; split at this <;> omega
    · have := (lev2 (by omega)).1; have h2 := hl2; simp only [Nat.reduceAdd] at h2; rw [this] at h2
      split at h2 <;> omega
    · omega
  · -- `D ≥ 1`: `t* ≥ 2`
    have hsi : 1 ≤ si := by
      rcases Nat.eq_zero_or_pos si with h0 | h0
      · subst h0; have := hl0; rw [a0] at this; split at this <;> omega
      · exact h0
    exact ⟨hsi, hN1 hsi⟩
  · subst h
    -- `t* = 3`
    have hsi : si = 2 := by
      rcases (show si = 0 ∨ si = 1 ∨ si = 2 by omega) with h | h | h
      · subst h; have := hl0; rw [a0] at this; simp at this
      · subst h; have := (lev2 (by omega)).1; have h2 := hl2; simp only [Nat.reduceAdd] at h2; rw [this] at h2
        simp at h2
      · exact h
    subst hsi
    obtain ⟨l2, l1, he1, l0⟩ := lev2 (by omega)
    have hm2 := hstep 2 (by omega) (by omega)
    obtain ⟨he2, -, -, -, -, r2⟩ := hlev 2 (Or.inr rfl) hm2
    have h3 : s.row 3 lv2 = 1 := by simpa using hl2
    rw [h3, l2, l1] at r2
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add] at r2
    have he1' : s.row 1 enter = 1 := by
      rw [hPl] at r2
      rcases (show s.row 1 enter = 0 ∨ s.row 1 enter = 1 by omega) with h | h
      · rw [h] at r2; simp at r2
      · exact h
    have Fm := F 2 (by omega)
    have := hnN 2 (by omega) (by omega) (by omega) (by omega)
    rw [show N1 = 11 + 1 from rfl] at this
    rw [show s.row 2 lv0 = 0 by omega, l1, he1', l2, sN 2 (by omega) 1 (by omega)] at this
    exact ⟨rfl, hm2, by simpa using this⟩

include G hw hs hL in
/-- **A row's edge**: a step or absent-by-key row's edge (not a `START`-`DOWN` edge) is an edge of its
record. -/
theorem rowEdge (i : Nat) (hi : i < 4) (hm : s.row i mS = 1 ∨ s.row i mK = 1)
    (hnh : s.row i nib ≠ SYM_START ∨ s.row i ek ≠ EK_DOWN) :
    ∃ r, vs[s.row i nN]? = some r ∧ [s.row i nN, s.row i nI, s.row i nib, s.row i nN2, s.row i nI2, s.row i ek] ∈
      edgesOf3 (s.row i nN) r := by
  have hst := upsWalk_step s hi
  have Mc := mode_cases (wRowF hw hs hL i hi).modes i
  have hmode : ((upsWalk s).step i).mode ≤ 1 := by
    rw [hst]; rcases hm with h | h
    · have := Mc.1.2 h; omega
    · have := Mc.2.1.2 h; omega
  obtain ⟨sN', hsN, he⟩ := Walk3.node_edge G (upsWalk_mem (s := s) hs) (i := i) (by rw [upsWalk_len]; exact hi) hmode
    (by rw [hst]; simpa [stepOf] using hnh)
  rw [hst] at hsN he
  simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero] at hsN he
  exact ⟨sN', hsN, he⟩

include G hw hs hL in
/-- The symbol of a step row is its walk symbol. -/
theorem stepSym (i : Nat) (hi : i < 4) (hm : s.row i mS = 1) : s.row i nib = wsym i := by
  have hst := upsWalk_step s hi
  have Mc := mode_cases (wRowF hw hs hL i hi).modes i
  have hok := Walk3.row_ok G (upsWalk_mem (s := s) hs) (i := i) (by rw [upsWalk_len]; exact hi)
  rw [hst] at hok
  have := (hok.stepE (Mc.1.2 hm)).1
  simpa [stepOf] using this

include G hw hs hL hP in
/-- **A branch on the path has a revealed child in its descend slot.** -/
theorem ups_downSlot (sd : Nat) (hsd : sd < di) :
    ∃ r, vs[s.row 0 (11 + sd)]? = some r ∧ ∀ sv kids m, r.v = .branch sv kids m →
      ∃ c l r pre po, kids[UpsRows.slotOf sd]? = some (NKid.node c l r pre po) := by
  obtain ⟨hle, hD1, hD2, -⟩ := ups_levels hw hs hL hP
  have i3 := hP.ix.2.2.1
  -- the row of level `sd`: `W1` for `sd = 0`, `W2` for `sd = 1`
  obtain ⟨i, hi, hm, hN, hsym, hsl, -⟩ : ∃ i, i < 4 ∧ s.row i mS = 1 ∧ s.row i nN = s.row 0 (11 + sd) ∧
      wsym i ≠ SYM_START ∧ wsym i = UpsRows.slotOf sd ∧ True := by
    rcases (show sd = 0 ∨ sd = 1 by omega) with rfl | rfl
    · obtain ⟨-, h1, h2⟩ := hD1 (by omega)
      exact ⟨1, by omega, h1, h2, by decide, by decide, trivial⟩
    · obtain ⟨-, h1, h2⟩ := hD2 (by omega)
      exact ⟨2, by omega, h1, h2, by decide, by decide, trivial⟩
  have hsy := stepSym G hw hs hL i hi hm
  obtain ⟨r, hr, he⟩ := rowEdge G hw hs hL i hi (Or.inl hm) (Or.inl (by rw [hsy]; exact hsym))
  rw [hN] at hr he
  refine ⟨r, hr, fun sv kids m hv => ?_⟩
  have hσ : s.row i nib ≠ SYM_END := by
    rw [hsy, hsl]; unfold UpsRows.slotOf; split <;> decide
  obtain ⟨c, l, r, pre, po, hk⟩ := edge_branch hv he (by simpa using hσ)
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hk
  rw [hsy, hsl] at hk
  exact ⟨c, l, r, pre, po, hk⟩

include G hw hs hL hP in
/-- **An absent-by-key terminal's edge** is an edge of `N_D`: `LEND` for `LSa`, else `KEY` at `I`. -/
theorem ups_termEdge (hc : 4 ≤ ci) :
    ∃ r, vs[s.row 0 (11 + di)]? = some r ∧
      (ci = 4 → ∃ e, e ∈ edgesOf3 (s.row 0 (11 + di)) r ∧ e.getD 5 0 = EK_LEND) ∧
      (ci ≠ 4 → ∃ e, e ∈ edgesOf3 (s.row 0 (11 + di)) r ∧ e.getD 5 0 = EK_KEY ∧
        e.getD 1 0 = ti) := by
  obtain ⟨-, -, -, hT3, -, hnI, -, -, -, hK, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨-, -, -, hNT⟩ := ups_levels hw hs hL hP
  have i4 := hP.ix.2.2.2
  have hmK : s.row (si + 1) mK = 1 := by rw [hT3, if_pos hc]
  obtain ⟨hL4, hK4⟩ := hK hc
  have hek : s.row (si + 1) ek ≠ EK_DOWN := by
    by_cases h4 : ci = 4
    · rw [hL4 h4]; decide
    · rw [(hK4 h4).1]; decide
  obtain ⟨r, hr, he⟩ := rowEdge G hw hs hL (si + 1) (by omega) (Or.inr hmK) (Or.inr hek)
  rw [hNT] at hr he
  refine ⟨r, hr, fun h4 => ⟨_, he, by simp [hL4 h4]⟩, fun h4 => ⟨_, he, by simp [(hK4 h4).1], by simp [hnI]⟩⟩

include G hw hs hL hP in
/-- **An absent-at-branch terminal's `BMAP` message** is `N_D`'s: `hasVal = 0` on `W3`, bit `y` clear on
`W1`/`W2`. -/
theorem ups_termBmap (hc : ci = 2 ∨ ci = 3) :
    ∃ r, vs[s.row 0 (11 + di)]? = some r ∧ ∃ bm hv,
      r.v.bmap = some (bm, hv) ∧ (si = 2 → hv = 0) ∧
      (si < 2 → bm / 2 ^ UpsSpec.yOf si % 2 = 0) := by
  obtain ⟨-, -, hT2, -, -, -, -, -, -, -, -⟩ := ups_walkTerm hw hs hL hP
  obtain ⟨-, -, -, hNT⟩ := ups_levels hw hs hL hP
  have i4 := hP.ix.2.2.2
  have hmB : s.row (si + 1) mB = 1 := by rw [hT2, if_pos hc]
  have hst := upsWalk_step s (i := si + 1) (by omega)
  have Mc := mode_cases (wRowF hw hs hL (si + 1) (by omega)).modes (si + 1)
  have hmode : ((upsWalk s).step (si + 1)).mode = 2 := by rw [hst]; exact Mc.2.2.1.2 hmB
  have hwv := upsWalk_mem (ws := ws) (s := s) hs
  obtain ⟨n, hn, he0, hbm⟩ := Walk3.bmap_provided3 G.node G.walk G.balB G.rowsP hwv
    (Walk3.row_mem (wv := upsWalk s) (i := si + 1) (by rw [upsWalk_len]; omega)) hmode
  have hok := Walk3.row_ok G hwv (i := si + 1) (by rw [upsWalk_len]; omega)
  obtain ⟨-, -, -, hlast, hnl⟩ := hok.absB hmode
  rw [hst] at he0 hbm hlast hnl
  simp only [stepOf, List.getD_cons_zero] at he0 hbm hlast hnl
  rw [hNT] at he0
  subst he0
  refine ⟨_, List.getElem?_eq_getElem hn, _, _, hbm, fun h2 => hlast (by subst h2; simp [upsWalk_len]), fun h2 => ?_⟩
  have := (hnl (by simp [upsWalk_len]; omega)).2
  rcases (show si = 0 ∨ si = 1 by omega) with rfl | rfl
  · simpa [wsym, UpsSpec.yOf, UpsSpec.key] using this
  · simpa [wsym, UpsSpec.yOf, UpsSpec.key] using this

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
