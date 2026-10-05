import ZkFormal.Sha.Statements

/-!
# ZkFormal.Sha.Frame.Chain — the block chain ending at a digest row

`chainStmt_of : KindStmt → BlockStmt → ChainStmt`.  Walking back from a `D`
row: the 16 rows before it are `R0..R15` (`D` follows `R15`, `Rj+1` follows
`Rj`, row 0 is never a round/digest row), and the row before `R0` is either a
start row (the chain ends) or a `D` row with `Last = 0` (continue).
-/

namespace ZkFormal.Sha.Frame

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View

variable {tr : Trace Fp} {t : Nat}

theorem next_of_lt {r : Nat} (h : r + 1 < tr.height t) : (r + 1) % tr.height t = r + 1 :=
  Nat.mod_eq_of_lt h

/-- `Rj` at row `r` means `R0` at row `r - j`. -/
theorem back_R (hK : KindFacts tr t) :
    ∀ j r, r < tr.height t → nv tr t r (colR j) = 1 → j < 16 → j ≤ r ∧ nv tr t (r - j) (colR 0) = 1 := by
  intro j
  induction j with
  | zero => intro r _ h _; exact ⟨Nat.zero_le _, by simpa using h⟩
  | succ j ih =>
    intro r hr h hj
    have hr0 : r ≠ 0 := by
      intro e; subst e; have := hK.first.1 (j + 1) hj; omega
    have hs := hK.stepR (r - 1) (by omega) j (by omega)
    rw [show r - 1 + 1 = r by omega, Nat.mod_eq_of_lt hr, h] at hs
    have := ih (r - 1) (by omega) hs.symm (by omega)
    exact ⟨by omega, by rw [show r - (j + 1) = r - 1 - j by omega]; exact this.2⟩

/-- A `D` row closes a block starting 16 rows earlier. -/
theorem back_D (hK : KindFacts tr t) {d : Nat} (hd : d < tr.height t) (hD : nv tr t d colD = 1) :
    16 ≤ d ∧ nv tr t (d - 16) (colR 0) = 1 := by
  have hd0 : d ≠ 0 := by intro e; subst e; have := hK.first.2; omega
  have hs := hK.stepD (d - 1) (by omega)
  rw [show d - 1 + 1 = d by omega, Nat.mod_eq_of_lt hd, hD] at hs
  have := back_R hK 15 (d - 1) (by omega) hs.symm (by omega)
  exact ⟨by omega, by rw [show d - 16 = d - 1 - 15 by omega]; exact this.2⟩

/-- The row before an `R0` is `S`, or `D` with `Last = 0`. -/
theorem before_R0 (hK : KindFacts tr t) {s : Nat} (hs : s < tr.height t) (h0 : nv tr t s (colR 0) = 1) :
    1 ≤ s ∧ (nv tr t (s - 1) colS = 1 ∨ (nv tr t (s - 1) colD = 1 ∧ nv tr t (s - 1) colLast = 0)) := by
  have hs0 : s ≠ 0 := by intro e; subst e; have := hK.first.1 0 (by omega); omega
  have hst := hK.stepR0 (s - 1) (by omega)
  rw [show s - 1 + 1 = s by omega, Nat.mod_eq_of_lt hs, h0] at hst
  refine ⟨by omega, ?_⟩
  by_cases hc : nv tr t (s - 1) colS = 1 ∨ (nv tr t (s - 1) colD = 1 ∧ nv tr t (s - 1) colLast = 0)
  · exact hc
  · rw [if_neg hc] at hst; omega

theorem getElem!_append_left' (l : List Nat) (x i : Nat) (h : i < l.length) :
    (l ++ [x])[i]! = l[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left h]

theorem getElem!_append_right' (l : List Nat) (x : Nat) : (l ++ [x])[l.length]! = x := by
  simp [List.getElem!_eq_getElem?_getD]

theorem getLast!_eq (l : List Nat) (h : l ≠ []) : l.getLast! = l[l.length - 1]! := by
  rw [List.getLast!_eq_getLast?_getD, List.getLast?_eq_getElem?, List.getElem!_eq_getElem?_getD]

theorem head!_append (l : List Nat) (x : Nat) (h : l ≠ []) : (l ++ [x]).head! = l.head! := by
  cases l with
  | nil => exact absurd rfl h
  | cons y ys => rfl

/-- The chain property, for any `D` row (not only last ones). -/
theorem chain_aux (hK : KindFacts tr t) :
    ∀ fuel d, d < tr.height t → nv tr t d colD = 1 → d < 17 * fuel →
      let ss := chainStarts tr t fuel d
      ss ≠ [] ∧ (∀ s ∈ ss, s < tr.height t ∧ nv tr t s (colR 0) = 1) ∧
      1 ≤ ss.head! ∧ nv tr t (ss.head! - 1) colS = 1 ∧
      (∀ i, i + 1 < ss.length → ss[i]! + 17 = ss[i + 1]!) ∧
      ss.getLast! + 16 = d := by
  intro fuel
  induction fuel with
  | zero => intro d _ _ h; omega
  | succ f ih =>
    intro d hd hD hf
    obtain ⟨h16, hR0⟩ := back_D hK hd hD
    obtain ⟨h1, hprev⟩ := before_R0 hK (s := d - 16) (by omega) hR0
    simp only [chainStarts]
    by_cases hc : nv tr t (d - 17) colD = 1 ∧ 17 ≤ d
    · rw [if_pos hc]
      obtain ⟨hne, hmem, hh1, hS, hstep, hlast⟩ := ih (d - 17) (by omega) hc.1 (by omega)
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact hmem s hs
        · simp at hs; subst hs; exact ⟨by omega, hR0⟩
      · rw [head!_append _ _ hne]; exact hh1
      · rw [head!_append _ _ hne]; exact hS
      · intro i hi
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hi' : i + 1 < (chainStarts tr t f (d - 17)).length
        · rw [getElem!_append_left' _ _ _ (by omega), getElem!_append_left' _ _ _ hi']
          exact hstep i hi'
        · have hiL : i + 1 = (chainStarts tr t f (d - 17)).length := by omega
          rw [getElem!_append_left' _ _ _ (by omega), hiL, getElem!_append_right']
          rw [getLast!_eq _ hne, show (chainStarts tr t f (d - 17)).length - 1 = i by omega] at hlast
          omega
      · rw [getLast!_eq _ (by simp)]
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel]
        rw [getElem!_append_right']; omega
    · rw [if_neg hc]
      have hS : nv tr t (d - 16 - 1) colS = 1 := by
        rcases hprev with h | h
        · exact h
        · exfalso; apply hc; exact ⟨by rw [show d - 17 = d - 16 - 1 by omega]; exact h.1, by omega⟩
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro s hs; simp at hs; subst hs; exact ⟨by omega, hR0⟩
      · show 1 ≤ d - 16; omega
      · exact hS
      · intro i hi; simp at hi
      · show d - 16 + 16 = d; omega

theorem chainStmt_of (hKs : KindStmt) : ChainStmt := by
  intro tr t pub hL d hd hD
  have hK := hKs tr t pub hL
  exact chain_aux hK (tr.height t) d hd hD.1 (by omega)

end ZkFormal.Sha.Frame
