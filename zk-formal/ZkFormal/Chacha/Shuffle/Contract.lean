import ZkFormal.Chacha.Shuffle.Sound

/-!
# ZkFormal.Chacha.Shuffle.Contract — `shuffle_contract`
-/

namespace ZkFormal.Chacha.Shuffle

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table NearSpecV3

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

section
variable (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
  (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub)
  {f d : Nat} (hf : f < tr.height t) (hfin : cv tr t f colFin = 1) (I : Inst tr t f d)
include hB hM hL hG hH hf hfin I

/-- The values read on the rows of the instance are those of the Fisher–Yates arrays. -/
theorem reads_fy :
    ∀ c, c ≤ d →
      (fyBefore (fun q => cv tr t (f - q) colJ) d
        ((List.range (d + 1)).map fun x => tr.cell t (f - x) colV0) c)[c]? = some (tr.cell t (f - c) colC) ∧
      (1 ≤ c → cv tr t (f - c) colJ < c →
        (fyBefore (fun q => cv tr t (f - q) colJ) d
          ((List.range (d + 1)).map fun x => tr.cell t (f - x) colV0) c)[cv tr t (f - c) colJ]? =
          some (tr.cell t (f - c) colO)) := by
  generalize hjs : (fun q => cv tr t (f - q) colJ) = js
  generalize hl : ((List.range (d + 1)).map fun x => tr.cell t (f - x) colV0) = l
  have hlen : l.length = d + 1 := by rw [← hl]; simp
  have hj : ∀ q, 1 ≤ q → q ≤ d → js q ≤ q := fun q h1 h2 => by
    rw [← hjs]; exact (step_s2 hL hG hH hf hfin I h1 h2).1
  have hlx : ∀ x, x ≤ d → l[x]? = some (tr.cell t (f - x) colV0) := fun x hx => by
    rw [← hl]; simp [show x < d + 1 by omega]
  -- one read: position `x` at time `c`, value `v`
  have one : ∀ c, c ≤ d → (∀ c', c < c' → c' ≤ d → (fyBefore js d l c')[c']? = some (tr.cell t (f - c') colC)) →
      ∀ x, (x = c ∨ (1 ≤ c ∧ js c = x ∧ x < c)) →
      (fyBefore js d l c)[x]? = some (tr.cell t (f - c) (if c = x then colC else colO)) := by
    intro c hc ih x hx
    have hxd : x ≤ d := by omega
    have RL := read_latest B hB hL hG hH hM hf hfin I hxd
    simp only at RL
    have hR : c ≤ d ∧ (c = x ∨ (1 ≤ c ∧ cv tr t (f - c) colJ = x ∧ x < c)) := by
      refine ⟨hc, ?_⟩
      rcases hx with h | ⟨h1, h2, h3⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨h1, by rw [← h2, ← hjs], h3⟩
    obtain ⟨hW, hgt, vA, vB, hmin⟩ := RL c hR
    generalize hcs : (if c = x then cv tr t (f - c) colT1 else cv tr t (f - c) colT2) = cs at hW hgt vA vB hmin
    have hjs' : ∀ q, cv tr t (f - q) colJ = js q := fun q => by rw [← hjs]
    rcases hW with h | ⟨h1, h2, h3, h4⟩
    · -- the input value
      rw [vA h, fyBefore_get js d l (by omega) hj (by omega) (by rcases hx with h' | h' <;> omega)]
      rw [lastW_none js d c x (fun q' h1 h2 hq' => by
        have := hmin q' (Or.inr ⟨by omega, h2, by rw [hjs']; exact hq'.1, hq'.2⟩) h1
        omega)]
      exact hlx x hxd
    · -- the value written by step `cs`
      rw [vB h2, fyBefore_get js d l (by omega) hj (by omega) (by rcases hx with h' | h' <;> omega)]
      rw [lastW_some js d c x cs hgt h2 (by rw [← hjs']; exact h3) h4 (fun q' hq1 hq2 hq' => by
        have := hmin q' (Or.inr ⟨by omega, by omega, by rw [hjs']; exact hq'.1, hq'.2⟩) hq1
        omega)]
      exact ih cs hgt h2
  -- strong induction from the top
  have main' : ∀ k c, d - c ≤ k → c ≤ d → (fyBefore js d l c)[c]? = some (tr.cell t (f - c) colC) := by
    intro k
    induction k with
    | zero =>
      intro c hk hc
      have := one c hc (fun c' h1 h2 => absurd h2 (by omega)) c (Or.inl rfl)
      simpa using this
    | succ k ihk =>
      intro c hk hc
      have := one c hc (fun c' h1 h2 => ihk c' (by omega) h2) c (Or.inl rfl)
      simpa using this
  have main : ∀ k c, d - c = k → c ≤ d → (fyBefore js d l c)[c]? = some (tr.cell t (f - c) colC) :=
    fun k c hk hc => main' k c (by omega) hc
  intro c hc
  refine ⟨main (d - c) c rfl hc, fun h1 h2 => ?_⟩
  have := one c hc (fun c' h1 h2 => main (d - c') c' rfl h2) (js c) (Or.inr ⟨h1, rfl, by rw [← hjs]; exact h2⟩)
  rw [← hjs] at this ⊢
  simp only [show ¬ (c = cv tr t (f - c) colJ) by omega, ite_false] at this
  exact this

end

theorem eval_outE {r : Nat} (hr : r < tr.height t) (heq : cv tr t r colEq = 0 ∨ cv tr t r colEq = 1) :
    outE.eval tr t r pub = if cv tr t r colEq = 1 then tr.cell t r colC else tr.cell t r colO := by
  rw [eval_eq]
  simp only [outE, zev_add, zev_mul, zev_sub, zev_k, zev_c, cur_cv]
  rcases heq with e | e <;> rw [e] <;> simp <;> rw [intCast_ofNat] <;> unfold cv <;> rw [Fp.ofNat_toNat]

/-- **`shuffle_contract`**: the instance ending at a final row `f` shuffles the inputs it
receives exactly as `NearSpecV3.shuffle` with the RNG state `rngAt key kstart`, and sends the
shuffled list. -/
theorem shuffle_contract (B : Buses) (hB : B.ok) (hL : SLocal tr t pub) (hG : GenRecv tr t pub)
    (hH : tr.height t ≤ 2 ^ 20) (hM : MemBal B tr t pub) {f : Nat} (hf : f < tr.height t)
    (hfin : cv tr t f colFin = 1) :
    ∃ L, 1 ≤ L ∧ L ≤ f + 1 ∧ L < 2 ^ 14 + 1 ∧ cv tr t f colL = L ∧
      (∀ x, x < L → cv tr t (f - x) colA = 1 ∧ cv tr t (f - x) colQ = x ∧
        cv tr t (f - x) colLid = cv tr t f colLid) ∧
      ∃ l', shuffle ((List.range L).map fun x => tr.cell t (f - x) colV0)
          (rngAt (skey tr t f) (cv tr t f colKs)) = some (l', rngAt (skey tr t f) (cv tr t f colKq)) ∧
        ∀ x, x < L → l'[x]? = some (outE.eval tr t (f - x) pub) := by
  obtain ⟨d, hdf, hd14, hfL, hst, rows⟩ := inst_rows hL hG hH hf hfin
  have I : Inst tr t f d := ⟨hdf, hd14, hfL, hst, rows⟩
  refine ⟨d + 1, by omega, by omega, by omega, hfL, fun x hx => ?_, ?_⟩
  · obtain ⟨a, q, -, -, lid, -⟩ := rows x (by omega); exact ⟨a, q, lid⟩
  generalize hjs : (fun q => cv tr t (f - q) colJ) = js
  generalize hl : ((List.range (d + 1)).map fun x => tr.cell t (f - x) colV0) = l
  have hlen : l.length = d + 1 := by rw [← hl]; simp
  have hj : ∀ q, 1 ≤ q → q ≤ d → js q ≤ q := fun q h1 h2 => by
    rw [← hjs]; exact (step_s2 hL hG hH hf hfin I h1 h2).1
  have RF := reads_fy B hB hL hG hH hM hf hfin I
  rw [hjs, hl] at RF
  -- the RNG states along the instance
  let rs : Nat → Rng := fun q => rngAt (skey tr t f) (cv tr t (f - q) colKq)
  have hgen : ∀ q, 1 ≤ q → q ≤ d → genIndex 64 (q + 1) (rs q) = some (js q, rs (q - 1)) := by
    intro q h1 h2
    obtain ⟨ha, hq, -, -, -, -, hkey, hfn, hkq⟩ := rows q h2
    obtain ⟨-, -, hg, -, -⟩ := step_info hG (show f - q < _ by omega) ha (hfn h1)
    rw [hq, hkey] at hg
    show genIndex 64 (q + 1) (rngAt (skey tr t f) (cv tr t (f - q) colKq)) = _
    rw [genIndex_rngAt, hg]
    show some (cv tr t (f - q) colJ, rngAt (skey tr t f) (cv tr t (f - q) colKn)) = some (js q, _)
    rw [← hjs, ← hkq h1, show f - q + 1 = f - (q - 1) by omega]
  have hloop := shuffleLoop_eq js rs d l hgen
  have hrs_d : rs d = rngAt (skey tr t f) (cv tr t f colKs) := by
    show rngAt _ (cv tr t (f - d) colKq) = _
    rw [(start_facts hL hH (show f - d < _ by omega) hst).2.1, (rows d (Nat.le_refl _)).2.2.2.2.2.1]
  have hrs_0 : rs 0 = rngAt (skey tr t f) (cv tr t f colKq) := by
    show rngAt _ (cv tr t (f - 0) colKq) = _; rw [Nat.sub_zero]
  refine ⟨fyLoop js d l, ?_, fun x hx => ?_⟩
  · unfold shuffle; rw [hlen, show d + 1 - 1 = d by omega, ← hrs_d, hloop, hrs_0]
  · have hr : f - x < tr.height t := by omega
    obtain ⟨ha, hq, -⟩ := rows x (by omega)
    have heq := bEq hL hr
    rw [eval_outE hr (by omega)]
    rcases Nat.eq_zero_or_pos x with h0 | hpos
    · subst h0
      have hff := fin_facts hL hf hfin
      rw [Nat.sub_zero, hff.2.1, if_pos rfl, fyLoop_eq_fyBefore]
      have := (RF 0 (Nat.zero_le _)).1; rwa [Nat.sub_zero] at this
    · rw [fyLoop_get js d l (by omega) hj hpos (by omega)]
      have hef := eqj_facts hL hr ha (by rw [hq]; omega) (by
        have := (step_s2 hL hG hH hf hfin I hpos (by omega)).1; omega)
      rw [hq] at hef
      rcases (show cv tr t (f - x) colEq = 0 ∨ cv tr t (f - x) colEq = 1 by omega) with e | e
      · rw [if_neg (by omega)]
        have hlt := hef.2 e
        have := (RF x (by omega)).2 hpos hlt
        rw [show js x = cv tr t (f - x) colJ by rw [← hjs]]; exact this
      · rw [if_pos e]
        have hjx := hef.1 e
        rw [show js x = x by rw [← hjs]; exact hjx]
        exact (RF x (by omega)).1

end ZkFormal.Chacha.Shuffle
