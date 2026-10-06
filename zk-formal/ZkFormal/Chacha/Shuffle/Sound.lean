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

/-! ## Writes of an instance -/

/-- The facts about the instance ending at `f` (`inst_rows`). -/
structure Inst (tr : Trace Fp) (t f d : Nat) : Prop where
  hdf : d ≤ f
  hd14 : d + 1 < 2 ^ 14
  hfL : cv tr t f colL = d + 1
  hst : cv tr t (f - d) colSt = 1
  rows : ∀ x, x ≤ d → cv tr t (f - x) colA = 1 ∧ cv tr t (f - x) colQ = x ∧
        cv tr t (f - x) colInst = f - d ∧ cv tr t (f - x) colL = d + 1 ∧
        cv tr t (f - x) colLid = cv tr t f colLid ∧ cv tr t (f - x) colKs = cv tr t f colKs ∧
        skey tr t (f - x) = skey tr t f ∧ (1 ≤ x → cv tr t (f - x) colFin = 0) ∧
        (1 ≤ x → cv tr t (f - x + 1) colKq = cv tr t (f - x) colKn)

theorem cv_of_cell {r r' x y : Nat} (h : tr.cell t r x = tr.cell t r' y) : cv tr t r x = cv tr t r' y := by
  unfold cv; rw [h]

section
variable (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
  (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub)
  {f d : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) (I : Inst tr t f d)
include hL hG hH hf hfin I

/-- A step row of the instance: `s2 = 1 ↔ j < q`, and `j ≤ q`. -/
theorem step_s2 {q : Nat} (hq1 : 1 ≤ q) (hq : q ≤ d) :
    cv tr t (f - q) colJ ≤ q ∧ (cv tr t (f - q) colS2 = 1 ↔ cv tr t (f - q) colJ < q) := by
  obtain ⟨ha, hqq, -, -, -, -, -, hfn, -⟩ := I.rows q hq
  have hr : f - q < tr.height t := by omega
  have hfn := hfn hq1
  obtain ⟨-, hj, -⟩ := step_info hG hr ha hfn
  rw [hqq] at hj
  have hs2 := s2_eq hL hr; rw [ha, hfn] at hs2
  have he := eqj_facts hL hr ha (by rw [hqq]; have := I.hd14; omega) (by have := I.hd14; omega)
  rw [hqq] at he
  have := bEq hL hr; have := bS2 hL hr
  refine ⟨hj, ?_⟩
  rcases (show cv tr t (f - q) colEq = 0 ∨ cv tr t (f - q) colEq = 1 by omega) with e | e
  · rw [e] at hs2; have := he.2 e; constructor <;> intro _ <;> simp at hs2 <;> omega
  · rw [e] at hs2; have := he.1 e; constructor <;> intro h <;> simp at hs2 <;> omega

include hB hM in
/-- **The write matching a read.**  A read on a row of the instance with message
`[inst, x, ts, v]` (`inst = f − d`, position `x`) is matched by the input write of position
`x` (stamp `d + 1`) or by the swap write of a step `q' > x` with `j_{q'} = x` (stamp `q'`). -/
theorem write_of {r : Nat} (hr : r < tr.height t) {i : Interaction} (hi : i ∈ B.is) (hb : i.bus = B.mem)
    (hs : i.send = false) (ha : i.multNat tr t r pub ≠ 0) {pos ts v : Nat}
    (hmsg : i.msgVal tr t r pub = [tr.cell t r colInst, tr.cell t r pos, tr.cell t r ts, tr.cell t r v])
    (hinst : cv tr t r colInst = f - d) (hpos : cv tr t r pos ≤ d) :
    (cv tr t r ts = d + 1 ∧ tr.cell t r v = tr.cell t (f - cv tr t r pos) colV0) ∨
    (∃ q', 1 ≤ q' ∧ q' ≤ d ∧ cv tr t (f - q') colJ = cv tr t r pos ∧ cv tr t r pos < q' ∧
      cv tr t r ts = q' ∧ tr.cell t r v = tr.cell t (f - q') colC) := by
  obtain ⟨r', hr', i', hi', hm', ha'⟩ := exists_write B hB hM hr hi hb hs ha
  rw [hmsg] at hm'
  rcases hi' with rfl | rfl
  · rw [msg_minit] at hm'
    simp only [List.cons.injEq] at hm'
    obtain ⟨e1, e2, e3, e4, -⟩ := hm'
    have ha1 : cv tr t r' colA = 1 := (mult_col rfl).mp ha'
    have hin := in_inst hL hG hH hf hfin I.hdf I.hst (fun x hx => (I.rows x hx).2.1) hr' ha1
      (by rw [cv_of_cell e1]; exact hinst)
    left
    have hq : cv tr t r' colQ = cv tr t r pos := cv_of_cell e2
    refine ⟨by rw [← cv_of_cell e3, show r' = f - (f - r') by omega, (I.rows (f - r') (by omega)).2.2.2.1], ?_⟩
    rw [← e4, ← hq, hin.2.2, show f - (f - r') = r' by omega]
  · rw [msg_mw2] at hm'
    simp only [List.cons.injEq] at hm'
    obtain ⟨e1, e2, e3, e4, -⟩ := hm'
    have hs1 : cv tr t r' colS2 = 1 := (mult_col rfl).mp ha'
    have ha1 : cv tr t r' colA = 1 := by
      have e := s2_eq hL hr'; rw [hs1] at e
      have := bA hL hr'; have := bFin hL hr'; have := bEq hL hr'
      rcases (show cv tr t r' colA = 0 ∨ cv tr t r' colA = 1 by omega) with h | h
      · rw [h] at e; simp at e
      · exact h
    have hin := in_inst hL hG hH hf hfin I.hdf I.hst (fun x hx => (I.rows x hx).2.1) hr' ha1
      (by rw [cv_of_cell e1]; exact hinst)
    right
    have hq' := hin.2.2
    have hrr : f - (f - r') = r' := by omega
    have hfin0 : cv tr t r' colFin = 0 := by
      have e := s2_eq hL hr'; rw [hs1, ha1] at e
      have := bFin hL hr'
      rcases (show cv tr t r' colFin = 0 ∨ cv tr t r' colFin = 1 by omega) with h | h
      · exact h
      · rw [h] at e; simp at e
    have hq1 : 1 ≤ f - r' := by
      rcases Nat.eq_zero_or_pos (f - r') with h | h
      · have : r' = f := by omega
        subst this; rw [hfin] at hfin0; simp at hfin0
      · exact h
    have hs := step_s2 hL hG hH hf hfin I (q := f - r') hq1 (by omega)
    rw [hrr] at hs
    refine ⟨f - r', hq1, by omega, by rw [hrr, cv_of_cell e2], ?_, ?_, ?_⟩
    · rw [← cv_of_cell e2]; exact hs.2.mp hs1
    · rw [← cv_of_cell e3, hq']
    · rw [← e4, hrr]

end

end ZkFormal.Chacha.Shuffle
