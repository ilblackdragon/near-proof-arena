import ZkFormal.Sha.Sound.Round
import ZkFormal.Sha.Compose

/-!
# ZkFormal.Sha.Sound.Block — `sha_block_sound` (`BlockStmt`)

An `R0` row `s` starts the rows `R0..R15, D` (`block_rows`); the schedule
words of the round rows are `Spec.Wt` of the block bytes (`sched_all`); the
`a`/`e` words of row `s - 1 + j` are `Spec.As/Es (4j + ·)` (`rounds_all`);
the `D` row is `compress` (`blockStmt`).
-/

namespace ZkFormal.Sha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View ZkFormal.Sha.Table
open ArenaCore.SHA256 ZkFormal.Sha.Spec

set_option linter.deprecated false

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Rows of a block -/

theorem next_row {r x : Nat} (hr : r < tr.height t) (h1 : nv tr t ((r + 1) % tr.height t) x = 1)
    (h0 : nv tr t 0 x = 0) : r + 1 < tr.height t ∧ nv tr t (r + 1) x = 1 := by
  by_cases h : r + 1 < tr.height t
  · rw [Nat.mod_eq_of_lt h] at h1; exact ⟨h, h1⟩
  · rw [show r + 1 = tr.height t by omega, Nat.mod_self] at h1; omega

theorem block_rows (hL : ShaLocal tr t pub) {s : Nat} (hs : s < tr.height t)
    (h0 : nv tr t s (colR 0) = 1) :
    1 ≤ s ∧ (∀ j, j < 16 → s + j < tr.height t ∧ nv tr t (s + j) (colR j) = 1) ∧
      s + 16 < tr.height t ∧ nv tr t (s + 16) colD = 1 := by
  have hK := kindStmt tr t pub hL
  have hs1 : 1 ≤ s := by
    have := hK.first.1 0 (by decide)
    by_cases h : s = 0
    · subst h; omega
    · omega
  have hrows : ∀ j, j < 16 → s + j < tr.height t ∧ nv tr t (s + j) (colR j) = 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨hs, h0⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      have := hK.stepR (s + j) h1 j (by omega)
      rw [h2] at this
      exact next_row h1 this (hK.first.1 (j + 1) hj)
  obtain ⟨h1, h2⟩ := hrows 15 (by decide)
  have := hK.stepD (s + 15) h1
  rw [h2] at this
  exact ⟨hs1, hrows, next_row h1 this hK.first.2⟩

/-! ## Block bytes and message words -/

theorem words_range' (g : Nat → Nat) : ∀ n a,
    words ((List.range' a (4 * n)).map g) =
      (List.range' a n 4).map (fun k => ((g k * 256 + g (k + 1)) * 256 + g (k + 2)) * 256 + g (k + 3)) := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    have e : List.range' a (4 * (n + 1)) = a :: (a + 1) :: (a + 2) :: (a + 3) :: List.range' (a + 4) (4 * n) := by
      rw [show 4 * (n + 1) = 4 * n + 1 + 1 + 1 + 1 by omega]
      simp only [List.range'_succ, Nat.add_assoc]
    rw [e, List.range'_succ]
    simp only [List.map_cons]
    rw [← ih (a + 4)]
    rfl

theorem bytes_recombine (W : Nat) (h : W < 2 ^ 32) :
    ((W / 2 ^ (8 * (3 - 0)) % 256 * 256 + W / 2 ^ (8 * (3 - 1)) % 256) * 256 +
      W / 2 ^ (8 * (3 - 2)) % 256) * 256 + W / 2 ^ (8 * (3 - 3)) % 256 = W := by
  simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.div_one]
  omega

/-- The decoded schedule word `W_u` of the block starting at `s`. -/
def Wd (tr : Trace Fp) (t s u : Nat) : Nat := wordAt tr t (s + u / 4) (colW (u % 4))

theorem Wd_eq {s u a b : Nat} (h1 : s + u / 4 = a) (h2 : u % 4 = b) :
    Wd tr t s u = wordAt tr t a (colW b) := by
  subst h1 h2; rfl

theorem wordAt_lt (tr : Trace Fp) (t r : Nat) (col : Nat → Nat) (h : ∀ b, b < 32 → nv tr t r (col b) ≤ 1) :
    wordAt tr t r col < 2 ^ 32 := ofBits_lt h

theorem blockBytes_words (hL : ShaLocal tr t pub) {s : Nat}
    (hrows : ∀ j, j < 16 → s + j < tr.height t ∧ nv tr t (s + j) (colR j) = 1) :
    ∀ u, u < 16 → (words (blockBytes tr t s)).getD u 0 = Wd tr t s u := by
  intro u hu
  unfold blockBytes
  rw [List.range_eq_range', show 64 = 4 * 16 from rfl, words_range']
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range', hu,
    Option.map_some, Option.getD_some, Nat.zero_add]
  have hb : ∀ k, k < 4 → byteAt tr t (s + (4 * u + k) / 16) ((4 * u + k) % 16) =
      Wd tr t s u / 2 ^ (8 * (3 - k)) % 256 := by
    intro k hk
    unfold byteAt
    rw [show (4 * u + k) / 16 = u / 4 by omega, show (4 * u + k) % 16 / 4 = u % 4 by omega,
      show (4 * u + k) % 16 % 4 = k by omega]
    rfl
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero] at h0
  rw [h0, hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)]
  have hlt : Wd tr t s u < 2 ^ 32 := wordAt_lt _ _ _ _ (fun b hb =>
    bool_of hL (hrows (u / 4) (by omega)).1 (mem_boolCols_lo (colW_lt (Nat.mod_lt _ (by decide)) hb)))
  exact bytes_recombine _ hlt

theorem blockBytes_length' (s : Nat) : (blockBytes tr t s).length = 64 := by
  simp [blockBytes]

/-! ## The schedule -/

theorem sched_all (hL : ShaLocal tr t pub) {s : Nat} (hs1 : 1 ≤ s)
    (hrows : ∀ j, j < 16 → s + j < tr.height t ∧ nv tr t (s + j) (colR j) = 1) :
    ∀ u, u < 64 → Wd tr t s u = Wt (blockBytes tr t s) u := by
  have hwl : (words (blockBytes tr t s)).length = 16 := words_length_16 _ (blockBytes_length' s)
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
  intro hu64
  by_cases hu : u < 16
  · rw [Wt_lt16 _ hwl u hu, blockBytes_words hL hrows u hu]
  obtain ⟨j, i, rfl, hi⟩ : ∃ j i, u = 4 * j + i ∧ i < 4 := ⟨u / 4, u % 4, by omega, by omega⟩
  have hj4 : 4 ≤ j := by omega
  have hj16 : j < 16 := by omega
  -- rows `s + j - 4 … s + j`
  have R : ∀ k, k ≤ 4 → s + j - k < tr.height t ∧ nv tr t (s + j - k) (colR (j - k)) = 1 := by
    intro k hk
    have := hrows (j - k) (by omega)
    rw [show s + (j - k) = s + j - k by omega] at this
    exact this
  have rr : ∀ k, 1 ≤ k → k ≤ 4 → s + j - k + 1 = s + j - (k - 1) := by intro k _ _; omega
  -- helper `I4` computed at row `s+j-4`
  have hI4 := help_I4 (r := s + j - 4) hL (by rw [rr 4 (by decide) (by decide)]; exact (R 3 (by decide)).1)
    (j := j - 3) (by omega) (by omega) (by rw [rr 4 (by decide) (by decide)]; exact (R 3 (by decide)).2) hi
  rw [rr 4 (by decide) (by decide)] at hI4
  have cp8 : ∀ l, l < 2 → nv tr t (s + j - 2) (colI8 i l) = nv tr t (s + j - 3) (colI4 i l) := by
    intro l hl
    have := help_copy (r := s + j - 3) hL (by rw [rr 3 (by decide) (by decide)]; exact (R 2 (by decide)).1)
      (j := j - 2) (by omega) (by omega) (by rw [rr 3 (by decide) (by decide)]; exact (R 2 (by decide)).2)
      (mem_I8 hi hl)
    rwa [rr 3 (by decide) (by decide)] at this
  have cp12 : ∀ l, l < 2 → nv tr t (s + j - 1) (colI12 i l) = nv tr t (s + j - 2) (colI8 i l) := by
    intro l hl
    have := help_copy (r := s + j - 2) hL (by rw [rr 2 (by decide) (by decide)]; exact (R 1 (by decide)).1)
      (j := j - 1) (by omega) (by omega) (by rw [rr 2 (by decide) (by decide)]; exact (R 1 (by decide)).2)
      (mem_I12 hi hl)
    rwa [rr 2 (by decide) (by decide)] at this
  have hI12 : pairW tr t (s + j - 1) (colI12 i) = ssig0 (w15W tr t (s + j - 4) i) +
      wordAt tr t (s + j - 4) (colW i) := by
    unfold pairW
    rw [cp12 0 (by decide), cp12 1 (by decide), cp8 0 (by decide), cp8 1 (by decide)]
    exact hI4.1
  have hb12 : nv tr t (s + j - 1) (colI12 i 0) < 2 ^ 17 ∧ nv tr t (s + j - 1) (colI12 i 1) < 2 ^ 17 := by
    rw [cp12 0 (by decide), cp12 1 (by decide), cp8 0 (by decide), cp8 1 (by decide)]
    exact hI4.2
  -- helper `W3` computed at row `s+j-2`
  have hW3 : i < 3 → pairW tr t (s + j - 1) (colW3 i) = wordAt tr t (s + j - 2) (colW (i + 1)) ∧
      nv tr t (s + j - 1) (colW3 i 0) < 65536 ∧ nv tr t (s + j - 1) (colW3 i 1) < 65536 := by
    intro hi3
    have := help_W3 (r := s + j - 2) hL (by rw [rr 2 (by decide) (by decide)]; exact (R 1 (by decide)).1)
      (j := j - 1) (by omega) (by omega) (by rw [rr 2 (by decide) (by decide)]; exact (R 1 (by decide)).2) hi3
    rwa [rr 2 (by decide) (by decide)] at this
  -- the schedule addition at row `s+j-1`
  have hst := sched_step (r := s + j - 1) hL (by rw [rr 1 (by decide) (by decide)]; exact (R 0 (by decide)).1)
    hj16 hj4 (by rw [rr 1 (by decide) (by decide)]; exact (R 0 (by decide)).2) hi hb12.1 hb12.2
    (fun h => (hW3 h).2)
  rw [rr 1 (by decide) (by decide), hI12, show s + j - (1 - 1) = s + j by omega] at hst
  -- index bookkeeping
  have e2 : w2W tr t (s + j - 1) i = Wt (blockBytes tr t s) (4 * j + i - 2) := by
    rw [← ih _ (by omega) (by omega)]
    unfold w2W; split
    · exact (Wd_eq (by omega) (by omega)).symm
    · exact (Wd_eq (by omega) (by omega)).symm
  have e7 : w7W tr t (s + j - 1) i = Wt (blockBytes tr t s) (4 * j + i - 7) := by
    rw [← ih _ (by omega) (by omega)]
    unfold w7W; split
    · rename_i h; rw [(hW3 h).1]; exact (Wd_eq (by omega) (by omega)).symm
    · exact (Wd_eq (by omega) (by omega)).symm
  have e15 : w15W tr t (s + j - 4) i = Wt (blockBytes tr t s) (4 * j + i - 15) := by
    rw [← ih _ (by omega) (by omega)]
    unfold w15W; split
    · exact (Wd_eq (by omega) (by omega)).symm
    · exact (Wd_eq (by omega) (by omega)).symm
  have e16 : wordAt tr t (s + j - 4) (colW i) = Wt (blockBytes tr t s) (4 * j + i - 16) := by
    rw [← ih _ (by omega) (by omega)]
    exact (Wd_eq (by omega) (by omega)).symm
  rw [e2, e7, e15, e16] at hst
  have hrec := Wt_rec' _ hwl (4 * j + i - 16)
  rw [show 4 * j + i - 16 + 16 = 4 * j + i by omega, show 4 * j + i - 16 + 14 = 4 * j + i - 2 by omega,
    show 4 * j + i - 16 + 9 = 4 * j + i - 7 by omega, show 4 * j + i - 16 + 1 = 4 * j + i - 15 by omega]
    at hrec
  rw [Wd_eq (s := s) (a := s + j) (b := i) (by omega) (by omega), hst, hrec]
  simp only [Nat.add_assoc]

/-! ## The rounds -/

theorem stateAt_getD (tr : Trace Fp) (t r : Nat) {w : Nat} (hw : w < 8) :
    (stateAt tr t r).getD w 0 = wordAt tr t r (colSt w) := by
  unfold stateAt
  simp [List.getD_eq_getElem?_getD, hw]

theorem colSt_A {w : Nat} (hw : w < 4) : colSt w = colA (3 - w) := by
  funext b; unfold colSt; simp [hw]

theorem colSt_E {w : Nat} (hw : 4 ≤ w) : colSt w = colE (7 - w) := by
  funext b; unfold colSt; simp [show ¬ w < 4 by omega]

/-- One slot of round row `Rj` (row `r + 1`), given the window so far. -/
theorem slot_step (hL : ShaLocal tr t pub) {r j i : Nat} (hr : r + 1 < tr.height t) (hj : j < 16)
    (hR : nv tr t (r + 1) (colR j) = 1) (hi : i < 4) (h bl : List Nat)
    (hW : wordAt tr t (r + 1) (colW i) = Wt bl (4 * j + i))
    (hwin : ∀ u, u < 4 + i → winW tr t r colA u = As h bl (4 * j + u) ∧
      winW tr t r colE u = Es h bl (4 * j + u)) :
    wordAt tr t (r + 1) (colA i) = As h bl (4 * j + i + 4) ∧
      wordAt tr t (r + 1) (colE i) = Es h bl (4 * j + i + 4) := by
  have st := round_step (pub := pub) hL hr hj hR hi
  obtain ⟨a0, e0⟩ := hwin i (by omega)
  obtain ⟨a1, e1⟩ := hwin (i + 1) (by omega)
  obtain ⟨a2, e2⟩ := hwin (i + 2) (by omega)
  obtain ⟨a3, e3⟩ := hwin (i + 3) (by omega)
  rw [show 4 * j + (i + 1) = 4 * j + i + 1 by omega] at a1 e1
  rw [show 4 * j + (i + 2) = 4 * j + i + 2 by omega] at a2 e2
  rw [show 4 * j + (i + 3) = 4 * j + i + 3 by omega] at a3 e3
  rw [a0, a1, a2, a3, e0, e1, e2, e3, hW] at st
  rw [As_succ4, Es_succ4]
  exact st

theorem rounds_all (hL : ShaLocal tr t pub) {s : Nat} (hs1 : 1 ≤ s)
    (hrows : ∀ j, j < 16 → s + j < tr.height t ∧ nv tr t (s + j) (colR j) = 1)
    (hW : ∀ u, u < 64 → Wd tr t s u = Wt (blockBytes tr t s) u) :
    ∀ j, j ≤ 16 → ∀ u, u < 4 →
      wordAt tr t (s - 1 + j) (colA u) = As (stateAt tr t (s - 1)) (blockBytes tr t s) (4 * j + u) ∧
      wordAt tr t (s - 1 + j) (colE u) = Es (stateAt tr t (s - 1)) (blockBytes tr t s) (4 * j + u) := by
  intro j
  induction j with
  | zero =>
    intro _ u hu
    simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add]
    have g := fun w (hw : w < 8) => stateAt_getD tr t (s - 1) hw
    rcases (by omega : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3) with rfl | rfl | rfl | rfl
    · show _ = (stateAt tr t (s - 1)).getD 3 0 ∧ _ = (stateAt tr t (s - 1)).getD 7 0
      rw [g 3 (by decide), g 7 (by decide), colSt_A (by decide), colSt_E (by decide)]
      exact ⟨rfl, rfl⟩
    · show _ = (stateAt tr t (s - 1)).getD 2 0 ∧ _ = (stateAt tr t (s - 1)).getD 6 0
      rw [g 2 (by decide), g 6 (by decide), colSt_A (by decide), colSt_E (by decide)]
      exact ⟨rfl, rfl⟩
    · show _ = (stateAt tr t (s - 1)).getD 1 0 ∧ _ = (stateAt tr t (s - 1)).getD 5 0
      rw [g 1 (by decide), g 5 (by decide), colSt_A (by decide), colSt_E (by decide)]
      exact ⟨rfl, rfl⟩
    · show _ = (stateAt tr t (s - 1)).getD 0 0 ∧ _ = (stateAt tr t (s - 1)).getD 4 0
      rw [g 0 (by decide), g 4 (by decide), colSt_A (by decide), colSt_E (by decide)]
      exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro hj
    have cur := ih (by omega)
    have hr1 : s - 1 + j + 1 = s + j := by omega
    have hr : s - 1 + j + 1 < tr.height t := by rw [hr1]; exact (hrows j (by omega)).1
    have hR : nv tr t (s - 1 + j + 1) (colR j) = 1 := by rw [hr1]; exact (hrows j (by omega)).2
    have slots : ∀ i, i ≤ 4 → ∀ i', i' < i →
        wordAt tr t (s - 1 + j + 1) (colA i') =
          As (stateAt tr t (s - 1)) (blockBytes tr t s) (4 * j + i' + 4) ∧
        wordAt tr t (s - 1 + j + 1) (colE i') =
          Es (stateAt tr t (s - 1)) (blockBytes tr t s) (4 * j + i' + 4) := by
      intro i
      induction i with
      | zero => intro _ i' h; omega
      | succ i ihi =>
        intro hi i' hi'
        by_cases hlt : i' < i
        · exact ihi (by omega) i' hlt
        have hii : i' = i := by omega
        subst hii
        refine slot_step hL hr (by omega) hR (by omega) _ _ ?_ ?_
        · rw [hr1, ← hW _ (by omega)]
          exact (Wd_eq (by omega) (by omega)).symm
        · intro u hu
          unfold winW
          split
          · exact cur u (by assumption)
          · have := ihi (by omega) (u - 4) (by omega)
            rw [show 4 * j + (u - 4) + 4 = 4 * j + u by omega] at this
            exact this
    intro u hu
    rw [show s - 1 + (j + 1) = s - 1 + j + 1 by omega, show 4 * (j + 1) + u = 4 * j + u + 4 by omega]
    exact slots 4 (Nat.le_refl _) u hu

/-! ## The digest row -/

theorem blockStmt : BlockStmt := by
  intro tr t pub hL s hs h0
  obtain ⟨hs1, hrows, hD16, hD⟩ := block_rows hL hs h0
  refine ⟨hs1, hD16, fun j hj => (hrows j hj).2, hD, ?_⟩
  have hW := sched_all hL hs1 hrows
  have hR := rounds_all hL hs1 hrows hW
  -- the chaining value carried by `Hin`
  have hin : ∀ w, w < 8 → ∀ j, j ≤ 15 →
      pairW tr t (s + j) (colHin w) = (stateAt tr t (s - 1)).getD w 0 ∧
      nv tr t (s + j) (colHin w 0) < 65536 ∧ nv tr t (s + j) (colHin w 1) < 65536 := by
    intro w hw j
    induction j with
    | zero =>
      intro _
      have hr1 : s - 1 + 1 = s := by omega
      have := hin_R0 (r := s - 1) (pub := pub) hL (by rw [hr1]; exact hs)
        (by rw [hr1]; exact h0) hw
      rw [hr1, ← stateAt_getD tr t (s - 1) hw] at this
      exact this
    | succ j ih =>
      intro hj
      have cp : ∀ l, l < 2 → nv tr t (s + (j + 1)) (colHin w l) = nv tr t (s + j) (colHin w l) := fun l hl =>
        help_copy (r := s + j) hL (hrows (j + 1) (by omega)).1 (j := j + 1) (by omega) (by omega)
          (hrows (j + 1) (by omega)).2 (mem_HinCopy hw hl)
      unfold pairW
      rw [cp 0 (by decide), cp 1 (by decide)]
      exact ih (by omega)
  have fin : ∀ w, w < 8 → wordAt tr t (s + 16) (colSt w) =
      add32 ((stateAt tr t (s - 1)).getD w 0)
        (if w < 4 then As (stateAt tr t (s - 1)) (blockBytes tr t s) (67 - w)
          else Es (stateAt tr t (s - 1)) (blockBytes tr t s) (71 - w)) := by
    intro w hw
    obtain ⟨hp, hb0, hb1⟩ := hin w hw 15 (by decide)
    have hd := digest_step (r := s + 15) (pub := pub) hL hD16 hD hw hb0 hb1
    rw [hd, hp, add32_eq]
    congr 2
    have hs15 : s + 15 = s - 1 + 16 := by omega
    rw [hs15]
    split
    · rename_i h
      rw [colSt_A h, (hR 16 (by decide) (3 - w) (by omega)).1, show 4 * 16 + (3 - w) = 67 - w by omega]
    · rename_i h
      rw [colSt_E (by omega), (hR 16 (by decide) (7 - w) (by omega)).2,
        show 4 * 16 + (7 - w) = 71 - w by omega]
  have e8 : stateAt tr t (s + 16) = [wordAt tr t (s + 16) (colSt 0), wordAt tr t (s + 16) (colSt 1),
      wordAt tr t (s + 16) (colSt 2), wordAt tr t (s + 16) (colSt 3), wordAt tr t (s + 16) (colSt 4),
      wordAt tr t (s + 16) (colSt 5), wordAt tr t (s + 16) (colSt 6), wordAt tr t (s + 16) (colSt 7)] :=
    rfl
  rw [e8, compress_eq]
  rw [fin 0 (by decide), fin 1 (by decide), fin 2 (by decide), fin 3 (by decide), fin 4 (by decide),
    fin 5 (by decide), fin 6 (by decide), fin 7 (by decide)]
  simp only [Nat.reduceLT, Nat.reduceSub, ↓reduceIte]

end ZkFormal.Sha.Sound

namespace ZkFormal.Sha.Sound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View

/-- `sha_block_sound` with its sublemma discharged. -/
theorem sha_block_sound' {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub)
    {s : Nat} (hs : s < tr.height t) (h0 : nv tr t s (colR 0) = 1) :
    stateAt tr t (s + 16) = ArenaCore.SHA256.compress (stateAt tr t (s - 1)) (blockBytes tr t s) :=
  sha_block_sound blockStmt hL hs h0

end ZkFormal.Sha.Sound
