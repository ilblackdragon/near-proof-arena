import ZkFormal.Chacha.Shuffle.Mem
import ZkFormal.Chacha.ShuffleSpec

/-!
# ZkFormal.Chacha.Shuffle.Sound — `shuffle_contract`

For a final row `f` of `shufV3` (with `GenRecv` and the memory bus balanced inside the
table): the instance occupies rows `f − x`, `x < L`; with `l[x]` the input received at row
`f − x`, `NearSpecV3.shuffle l (rngAt key kstart) = some (l', rngAt key kend)` and the output
sent at row `f − x` is `l'[x]`.

Proof: offline memory checking (`ShuffleSpec.mem_latest`) makes every read return the latest
write; by induction on the steps (top down) the values read are those of the Fisher–Yates
arrays (`ShuffleSpec.fyBefore_get`), and the outputs are the final list (`fyLoop_get`).
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## `lastW` as a minimum -/

theorem find_range (p : Nat → Bool) (a : Nat) : ∀ (k m : Nat), m < k → p (a + m) = true →
    (∀ m', m' < m → p (a + m') = false) → ((List.range k).map (a + ·)).find? p = some (a + m)
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, m, hm, hp, hlt => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases m with
    | zero => rw [List.find?_cons_of_pos (by simpa using hp)]
    | succ m =>
      rw [List.find?_cons_of_neg (by have := hlt 0 (by omega); simp at this ⊢; exact this)]
      have := find_range p (a + 1) k m (by omega) (by rw [show a + 1 + m = a + (m + 1) by omega]; exact hp)
        (fun m' hm' => by rw [show a + 1 + m' = a + (m' + 1) by omega]; exact hlt (m' + 1) (by omega))
      rw [show a + 1 + m = a + (m + 1) by omega] at this
      rw [← this]; congr 1; apply List.map_congr_left; intro x _; simp [Function.comp]; omega

theorem lastW_none (js : Nat → Nat) (i q x : Nat)
    (h : ∀ q', q < q' → q' ≤ i → ¬ (js q' = x ∧ x < q')) : lastW js i q x = none := by
  unfold lastW
  rw [List.find?_eq_none]
  intro y hy
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
  have := List.mem_range.mp hd
  have := h (q + 1 + d) (by omega) (by omega)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact this

theorem lastW_some (js : Nat → Nat) (i q x q0 : Nat) (h1 : q < q0) (h2 : q0 ≤ i) (h3 : js q0 = x)
    (h4 : x < q0) (h : ∀ q', q < q' → q' < q0 → ¬ (js q' = x ∧ x < q')) : lastW js i q x = some q0 := by
  unfold lastW
  have := find_range (fun q' => js q' == x && decide (x < q')) (q + 1) (i - q) (q0 - (q + 1)) (by omega)
    (by rw [show q + 1 + (q0 - (q + 1)) = q0 by omega]; simp [h3, h4])
    (fun m' hm' => by
      have := h (q + 1 + m') (by omega) (by omega)
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      by_cases e : js (q + 1 + m') = x
      · exact Or.inr (fun hx => this ⟨e, hx⟩)
      · exact Or.inl e)
  rw [show q + 1 + (q0 - (q + 1)) = q0 by omega] at this
  rw [← this]

/-! ## The instance of a final row -/

section
variable (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
  (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub)
include hL hG hH

/-- Rows of the instance ending at the final row `f`. -/
theorem inst_rows {f : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) :
    ∃ d, d ≤ f ∧ d + 1 < 2 ^ 14 ∧ cv tr t f colL = d + 1 ∧ cv tr t (f - d) colSt = 1 ∧
      ∀ x, x ≤ d → cv tr t (f - x) colA = 1 ∧ cv tr t (f - x) colQ = x ∧
        cv tr t (f - x) colInst = f - d ∧ cv tr t (f - x) colL = d + 1 ∧
        cv tr t (f - x) colLid = cv tr t f colLid ∧ cv tr t (f - x) colKs = cv tr t f colKs ∧
        skey tr t (f - x) = skey tr t f ∧ (1 ≤ x → cv tr t (f - x) colFin = 0) ∧
        (1 ≤ x → cv tr t (f - x + 1) colKq = cv tr t (f - x) colKn) := by
  have ha := fin_a hL hf hfin
  obtain ⟨s, hs, hst, hall⟩ := walkStart hL hG hH f hf ha
  obtain ⟨-, -, -, qf, instf, Lf, lidf, ksf, keyf, -⟩ := hall f hs (Nat.le_refl _)
  have hq0 := (fin_facts hL hf hfin).1
  rw [hq0] at qf
  -- `q(s) = f − s`, `L = f − s + 1`
  have hstart := start_facts hL hH (show s < tr.height t by omega) hst
  have hd14 : f - s + 1 < 2 ^ 14 := by
    rcases Nat.eq_zero_or_pos (f - s) with h0 | h0
    · omega
    · obtain ⟨a1, f1, -, -⟩ := hall s (Nat.le_refl _) hs
      have := (step_info hG (show s < tr.height t by omega) a1 (f1 (by omega))).1
      omega
  have hLs : cv tr t s colL = f - s + 1 := by
    have := hstart.1; rw [← qf, Nat.mod_eq_of_lt (by omega)] at this; omega
  refine ⟨f - s, by omega, hd14, by rw [Lf, hLs], by rw [show f - (f - s) = s by omega]; exact hst,
    fun x hx => ?_⟩
  obtain ⟨ax, fx, -, qx, ix, Lx, lidx, ksx, keyx, kqx⟩ := hall (f - x) (by omega) (by omega)
  refine ⟨ax, by omega, by rw [ix]; omega, by rw [Lx, hLs], by rw [lidx, lidf], by rw [ksx, ksf],
    by rw [keyx, keyf], fun h => fx (by omega), fun h => ?_⟩
  exact kqx (by omega)

/-- An active row of the instance's memory (`inst = f − d`) is a row `f − x`, `x ≤ d`. -/
theorem in_inst {f d : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) (hd : d ≤ f)
    (hd1 : cv tr t (f - d) colSt = 1)
    (hall : ∀ x, x ≤ d → cv tr t (f - x) colQ = x)
    {r : Nat} (hr : r < tr.height t) (ha : cv tr t r colA = 1) (hi : cv tr t r colInst = f - d) :
    f - d ≤ r ∧ r ≤ f ∧ cv tr t r colQ = f - r := by
  obtain ⟨s, hs, hst, hall'⟩ := walkStart hL hG hH r hr ha
  obtain ⟨-, -, -, qr, ir, -⟩ := hall' r hs (Nat.le_refl _)
  have hs' : s = f - d := by rw [← ir, hi]
  subst hs'
  have hrf : r ≤ f := by
    apply Classical.byContradiction; intro h
    have := (hall' f (by omega) (by omega)).2.1 (by omega)
    omega
  have := hall (f - r) (by omega)
  rw [show f - (f - r) = r by omega] at this
  exact ⟨hs, hrf, this⟩

end

end ZkFormal.Chacha.Shuffle
