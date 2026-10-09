import ZkFormal.NearV3.Extract.Ups.PlanDefs
import ZkFormal.NearV3.Extract.Ups.FieldRows

/-!
# ZkFormal.NearV3.Extract.Ups.PlanRows — the part plan, row facts

The segment indices on `W0` (`segIx`: case, `I`, `D`, `t*`), the part indices on a part's
first row, the planned kind (`planDec`), and the transitions of `jo`, `rc`, `cN` at part
boundaries.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Constraint membership -/

theorem memSeg {e : Expr} (h : e ∈ cSeg) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))

theorem memWalk {e : Expr} (h : e ∈ cWalk) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))

theorem memMem {e : Expr} (h : e ∈ cMem) : e ∈ UpsV3.constraints := by
  unfold UpsV3.constraints; simp only [List.mem_append]; exact Or.inr h

theorem pure_sumc : ∀ xs : List Nat, (sumc xs).pure = true
  | [] => rfl
  | x :: xs => by
    have := pure_sumc xs
    simp only [sumc, List.map_cons, Dsl.sum] at this ⊢
    simp [Expr.pure, Dsl.c, this]

/-! ## One-hot groups -/

theorem ohGroup {C : URow} (base len : Nat) (hb : ∀ m, m < len → C (base + m) ≤ 1)
    (hs : ((List.range len).map fun m => C (base + m)).sum = 1) :
    ∃ i, i < len ∧ ∀ m, m < len → C (base + m) = if m = i then 1 else 0 := by
  have e : (List.range len).map (fun m => C (base + m)) = ((List.range len).map (base + ·)).map C := by
    simp [List.map_map, Function.comp_def]
  rw [e] at hs
  obtain ⟨i, hi, hall⟩ := oneHot_ix ((List.range len).map (base + ·)) (by
    intro x hx; simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨m, hm, rfl⟩ := hx; exact hb m hm) hs
  simp only [List.length_map, List.length_range] at hi hall
  refine ⟨i, hi, fun m hm => ?_⟩
  have := hall m hm
  simpa using this

theorem kinds_sub : ∀ x ∈ UpsV3.kinds, x ∈ partBools := by decide
theorem sd_sub : ∀ x ∈ [sd0, sd1, sd2], x ∈ partBools := by decide

theorem kinds_get : ∀ m, m < 12 → UpsV3.kinds[m]? = some (kcol m) := by decide
theorem kinds_len : UpsV3.kinds.length = 12 := rfl

/-- `nTE` on a row with known case and `I`. -/
theorem nTE_val {C D : URow} {ci ti : Nat} (h1 : ci < 11) (h2 : ti < 3)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0) :
    nev C D nTE = nTof ci ti := by
  -- the plan columns other than the case and `I` columns do not matter: take the row's own values
  have hag : ∀ x ∈ planCols, (fun y => if (17 ≤ y ∧ y < 28) ∨ (34 ≤ y ∧ y < 37) then C y else
      planRow ci ti 0 0 0 y) x = planRow ci ti 0 0 0 x := by
    intro x _
    simp only
    split
    · next h =>
      unfold planRow
      have h1 : ¬ (x = pf ∨ x = qb) := by rw [pf_v, qb_v]; omega
      rw [if_neg h1]
      rcases h with h | h
      · rw [if_pos h]; have := hcs (x - 17) (by omega); rwa [show 17 + (x - 17) = x by omega] at this
      · have h2 : ¬ (17 ≤ x ∧ x < 28) := by omega
        simp only [h2, h, ite_false, ite_true, and_self]
        have := hti (x - 34) (by omega); rwa [show 34 + (x - 34) = x by omega] at this
    · rfl
  rw [nev_congr (C' := fun y => if (17 ≤ y ∧ y < 28) ∨ (34 ≤ y ∧ y < 37) then C y else planRow ci ti 0 0 0 y)
    (D' := zrow) nTE (fun x hx => by simp only [nTE_sub x hx, ite_true]) (by rw [nTE_cols.2]; simp)]
  rw [nev_plan hag nTE_cols, nTDec h1 h2]


section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC

/-- A segment flag on `W0`. -/
theorem segBool (hsf : C sf = 1) {x : Nat} (hx : x ∈ segBools) : C x ≤ 1 := by
  have h := fact ok (e := Expr.mul (c sf) (Dsl.bool (c x))) (memBool (by
    unfold cBool; simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, rfl⟩))))))))
  uev_simp
  simp only [hsf] at h
  have e : Fp.ofNat 1 = 1 := rfl
  rw [e] at h
  exact le1 (nat01 (hC x) (by grind))

/-- A part flag on the part's first row (naturals). -/
theorem partBoolN (hpf : C pf = 1) {x : Nat} (hx : x ∈ partBools) : C x ≤ 1 :=
  le1 (partBool ok hC hpf hx)

include hD

theorem sumN {xs : List Nat} {G : Expr} (hG : nev C D G = 1) (hGp : G.pure = true)
    (hm : Expr.mul G (sub (sumc xs) (k 1)) ∈ UpsV3.constraints)
    (hb : ∀ x ∈ xs, C x ≤ 1) (hlen : xs.length ≤ 16) : (xs.map C).sum = 1 := by
  have hp : (Expr.mul G (sub (sumc xs) (k 1))).pure = true := by
    simp [Expr.pure, Dsl.sub, Dsl.k, Dsl.c, pure_sumc, hGp]
  have h := factN ok hC hD hm hp
  simp only [nev, Dsl.sub, Dsl.k, Dsl.c, hG, if_false, Bool.false_eq_true] at h
  have hs : nev C D (sumc xs) = (xs.map C).sum % P := by
    unfold sumc
    clear h hm hp
    induction xs with
    | nil => simp [Dsl.sum, nev]
    | cons x xs ih =>
      simp only [List.map_cons, Dsl.sum, nev, Dsl.c, if_false, Bool.false_eq_true, List.sum_cons]
      rw [ih (fun y hy => hb y (by simp [hy])) (by simp at hlen; omega)]
      rw [Nat.add_mod_mod]
  have hle : (xs.map C).sum ≤ xs.length := by
    clear h hm hs hp
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := hb x (by simp)
      have := ih (fun y hy => hb y (by simp [hy])) (by simp at hlen; omega)
      omega
  rw [hs] at h
  simp only [P_lit] at h
  have : (xs.map C).sum < 2013265921 := by omega
  rw [Nat.mod_eq_of_lt this] at h
  omega

/-- **The segment indices** on `W0`: case `ci`, `I = ti`, `D = di`, `t* = si + 1`. -/
theorem segIx (hsf : C sf = 1) : ∃ ci ti di si, ci < 11 ∧ ti < 3 ∧ di < 3 ∧ si < 3 ∧
    (∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0) ∧ (∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0) ∧
    (∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0) ∧ (∀ m, m < 3 → C (31 + m) = if m = si then 1 else 0) := by
  have grp := fun (base len : Nat) (xs : List Nat) (hxs : xs = (List.range len).map (base + ·))
      (hsub : ∀ m, m < len → base + m ∈ segBools)
      (hmem : Expr.mul (c sf) (sub (sumc xs) (k 1)) ∈ UpsV3.constraints)
      (hl : len ≤ 16) => by
    subst hxs
    exact
    ohGroup (C := C) base len (fun m hm => segBool ok hC hsf (hsub m hm)) (by
      have := sumN ok hC hD (G := c sf) (by simp [nev, Dsl.c, hsf]) rfl hmem (fun x hx => by
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨m, hm, rfl⟩ := hx; exact segBool ok hC hsf (hsub m hm)) (by simpa using hl)
      simpa [List.map_map, Function.comp_def] using this)
  obtain ⟨ci, h1, e1⟩ := grp 17 11 cases (by decide) (by decide) (memSeg (by simp [cSeg])) (by decide)
  obtain ⟨ti, h2, e2⟩ := grp 34 3 [ti0, ti1, ti2] (by decide) (by decide) (memSeg (by simp [cSeg])) (by decide)
  obtain ⟨di, h3, e3⟩ := grp 28 3 [dd0, dd1, dd2] (by decide) (by decide) (memSeg (by simp [cSeg])) (by decide)
  obtain ⟨si, h4, e4⟩ := grp 31 3 [ts1, ts2, ts3] (by decide) (by decide) (memSeg (by simp [cSeg])) (by decide)
  exact ⟨ci, ti, di, si, h1, h2, h3, h4, e1, e2, e3, e4⟩


/-- **The part indices** on a part's first row: kind `ki` (`kinds` order), source level `sdi`. -/
theorem partIx (hpf : C pf = 1) (hqb : C qb = 1) : ∃ ki sdi, ki < 12 ∧ sdi < 3 ∧
    (∀ m, m < 12 → C (kcol m) = if m = ki then 1 else 0) ∧ (∀ m, m < 3 → C (65 + m) = if m = sdi then 1 else 0) := by
  have hb := fun {x} (hx : x ∈ partBools) => partBoolN ok hC hpf hx
  have hG : nev C D (.mul (c qb) (c pf)) = 1 := by simp [nev, Dsl.c, hqb, hpf, P_lit]
  have hk := sumN ok hC hD (xs := UpsV3.kinds) hG rfl (memPlan (by simp [cPlan]))
    (fun x hx => hb (kinds_sub x hx)) (by decide)
  obtain ⟨ki, hki, hall⟩ := oneHot_ix UpsV3.kinds (fun x hx => hb (kinds_sub x hx)) hk
  have hs := sumN ok hC hD (xs := [sd0, sd1, sd2]) hG rfl (memPlan (by simp [cPlan]))
    (fun x hx => hb (sd_sub x hx)) (by decide)
  obtain ⟨sdi, hsdi, hall2⟩ := oneHot_ix [sd0, sd1, sd2] (fun x hx => hb (sd_sub x hx)) hs
  refine ⟨ki, sdi, by rw [kinds_len] at hki; exact hki, by simpa using hsdi, fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : m < UpsV3.kinds.length := by rw [kinds_len]; exact hm
    have e := hall m hm'
    have g : UpsV3.kinds[m]'hm' = kcol m := by
      have := kinds_get m hm; rw [List.getElem?_eq_getElem hm'] at this; simpa using this
    rw [g] at e; exact e
  · have e := hall2 m (by simpa using hm)
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> simpa [sd0, sd1, sd2] using e

/-- **The planned kind** on a part's first row. -/
theorem planFact {ci ti jj ki : Nat} (h1 : ci < 11) (h2 : ti < 3) (h3 : jj < 5) (h4 : ki < 12)
    (hpf : C pf = 1) (hqb : C qb = 1)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0)
    (hjo : ∀ m, m < 4 → C (61 + m) = if m + 1 = jj then 1 else 0)
    (hk : ∀ m, m < 12 → C (kcol m) = if m = ki then 1 else 0) :
    planOk ci ti jj ki (C UpsV3.up) = true := by
  have hu : C UpsV3.up ≤ 1 := partBoolN ok hC hpf (by decide)
  have hag := planAgree hpf hqb rfl hcs hti hjo hk
  apply planDec h1 h2 h3 h4 (by omega)
  · rw [← nev_plan (D := D) hag eKC_cols]; exact factN ok hC hD (memPlan (by simp [cPlan, eKC]))
  · rw [← nev_plan (D := D) hag eUT_cols]; exact factN ok hC hD (memPlan (by simp [cPlan, eUT]))
  · rw [← nev_plan (D := D) hag eUK_cols]; exact factN ok hC hD (memPlan (by simp [cPlan, eUK]))

theorem nev_DE {di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0) :
    nev C D DE = di := by
  have a1 := hdd 1 (by omega); have a2 := hdd 2 (by omega)
  simp only [DE]; nev_simp
  simp only [show (28 + 1 : Nat) = dd1 from rfl, show (28 + 2 : Nat) = dd2 from rfl] at a1 a2
  rw [a1, a2]
  rcases (show di = 0 ∨ di = 1 ∨ di = 2 by omega) with rfl | rfl | rfl <;> rfl

theorem nev_sdE {di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (65 + m) = if m = di then 1 else 0) :
    nev C D sdE = di := by
  have a1 := hdd 1 (by omega); have a2 := hdd 2 (by omega)
  simp only [sdE]; nev_simp
  simp only [show (65 + 1 : Nat) = sd1 from rfl, show (65 + 2 : Nat) = sd2 from rfl] at a1 a2
  rw [a1, a2]
  rcases (show di = 0 ∨ di = 1 ∨ di = 2 by omega) with rfl | rfl | rfl <;> rfl

theorem nev_sel3 {base off di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (base + m) = if m = di then 1 else 0) :
    nev C D (sum [.mul (c base) (c off), .mul (c (base + 1)) (c (off + 1)), .mul (c (base + 2)) (c (off + 2))]) =
      C (off + di) := by
  have a0 := hdd 0 (by omega); have a1 := hdd 1 (by omega); have a2 := hdd 2 (by omega)
  simp only [Nat.add_zero] at a0
  nev_simp
  rw [a0, a1, a2]
  have hP := hC (off + di); rw [P_lit] at hP
  rcases (show di = 0 ∨ di = 1 ∨ di = 2 by omega) with rfl | rfl | rfl <;> simp <;> omega

theorem nev_depDE {di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0) :
    nev C D depDE = C (176 + di) := nev_sel3 ok hC hD (base := 28) (off := 176) h hdd

theorem nev_depSE {di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (65 + m) = if m = di then 1 else 0) :
    nev C D depSE = C (176 + di) := nev_sel3 ok hC hD (base := 65) (off := 176) h hdd

theorem nev_Nsel {di : Nat} (h : di < 3) (hdd : ∀ m, m < 3 → C (65 + m) = if m = di then 1 else 0) :
    nev C D (sum [.mul (c sd0) (c N0), .mul (c sd1) (c N1), .mul (c sd2) (c N2)]) = C (11 + di) :=
  nev_sel3 ok hC hD (base := 65) (off := 11) h hdd

/-! ## Part header facts (first row) -/

/-- Depth, descend count, source level / record / depth on a part's first row. -/
theorem partHeadPlan {ci ti di ki sdi : Nat} (h1 : ci < 11) (h2 : ti < 3) (h3 : di < 3) (h4 : ki < 12) (h5 : sdi < 3)
    (hpf : C pf = 1) (hqb : C qb = 1)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0)
    (hdd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0)
    (hk : ∀ m, m < 12 → C (kcol m) = if m = ki then 1 else 0)
    (hsd : ∀ m, m < 3 → C (65 + m) = if m = sdi then 1 else 0) :
    (C UpsV3.up = 0 → C pdep = C (176 + di)) ∧
    (C UpsV3.up = 1 → (C pdep + C j) % P = (C (176 + di) + nTof ci ti) % P) ∧
    (C UpsV3.up = 0 → C rc = di) ∧
    (ki ≠ 11 → ki ≤ 1 → C rc = sdi + 1) ∧
    (ki ≠ 11 → 1 < ki → sdi = di) ∧
    (ki ≠ 11 → C sN = C (11 + sdi) ∧ C pdep = C (176 + sdi)) := by
  have hu : C UpsV3.up ≤ 1 := partBoolN ok hC hpf (by decide)
  have eT := nTE_val (D := D) h1 h2 hcs hti
  have eDE := nev_DE ok hC hD h3 hdd
  have edep := nev_depDE ok hC hD h3 hdd
  have esd := nev_sdE ok hC hD h5 hsd
  have esdep := nev_depSE ok hC hD h5 hsd
  have eN := nev_Nsel ok hC hD h5 hsd
  have kB : C kRDB = if 0 = ki then 1 else 0 := hk 0 (by omega)
  have kE : C kRDE = if 1 = ki then 1 else 0 := hk 1 (by omega)
  have kP : C kPT = if 11 = ki then 1 else 0 := hk 11 (by omega)
  have hTle := nTof_le ci h1 ti h2
  have hPl := P_lit
  have bC := fun x => hC x
  simp only [P_lit] at bC
  -- the constraints
  have f1 := factN ok hC hD (e := .mul (c pf) (.add (sub (c pdep) depDE) (.mul (c UpsV3.up) (sub (c j) nTE))))
    (memPlan (by simp [cPlan]))
  have f2 := factN ok hC hD (e := .mul (c pf) (.mul (not (c UpsV3.up)) (sub (c rc) DE))) (memPlan (by simp [cPlan]))
  have f3 := factN ok hC hD (e := mul3 (c pf) (not (c kPT)) (sub sdE (.add (.mul (not kRD) DE) (.mul kRD (sub (c rc) (k 1))))))
    (memPlan (by simp [cPlan]))
  have f4 := factN ok hC hD (e := mul3 (c pf) (not (c kPT))
    (sub (c sN) (sum [.mul (c sd0) (c N0), .mul (c sd1) (c N1), .mul (c sd2) (c N2)]))) (memPlan (by simp [cPlan]))
  have f5 := factN ok hC hD (e := mul3 (c pf) (not (c kPT)) (sub (c pdep) depSE)) (memPlan (by simp [cPlan]))
  have f4' : (C pf * ((1 % P + (P - C kPT) % P) % P) % P *
      ((C sN + (P - nev C D (sum [.mul (c sd0) (c N0), .mul (c sd1) (c N1), .mul (c sd2) (c N2)])) % P) % P)) % P = 0 := f4
  rw [eN] at f4'
  simp only [nev, Dsl.sub, Dsl.k, Dsl.c, Dsl.not, Dsl.mul3, kRD, ite_false, Bool.false_eq_true, eT, eDE, edep, esd,
    esdep, hpf, kB, kE, kP, P_lit] at f1 f2 f3 f4' f5
  have hj := bC j; have hpd := bC pdep; have hrc := bC rc; have hsN := bC sN
  have hd := bC (176 + di); have hd' := bC (176 + sdi); have hN := bC (11 + sdi)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h0 h1' => ?_, fun h0 h1' => ?_, fun h0 => ?_⟩
  · rw [h] at f1; simp at f1; omega
  · rw [h] at f1; simp at f1; rw [P_lit]; omega
  · rw [h] at f2; simp at f2; omega
  · rw [if_neg (by omega)] at f3
    rcases (show ki = 0 ∨ ki = 1 by omega) with rfl | rfl <;> simp at f3 <;> omega
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)] at f3; simp at f3; omega
  · rw [if_neg (by omega)] at f4' f5; simp at f4' f5; omega

/-! ## Boundaries -/

/-- After the value part: the first node part has `jo1`. -/
theorem joValueEnd (hvb : C vb = 1) (hpl : C pl = 1) :
    D (jo 1) = 1 ∧ D (jo 2) = 0 ∧ D (jo 3) = 0 ∧ D (jo 4) = 0 := by
  have f1 := factN ok hC hD (e := mul3 (c vb) (c pl) (sub (n (jo 1)) (k 1))) (memRows (by simp [cRows]))
  have f2 := factN ok hC hD (e := mul3 (c vb) (c pl) (n (jo 2))) (memRows (by simp [cRows]))
  have f3 := factN ok hC hD (e := mul3 (c vb) (c pl) (n (jo 3))) (memRows (by simp [cRows]))
  have f4 := factN ok hC hD (e := mul3 (c vb) (c pl) (n (jo 4))) (memRows (by simp [cRows]))
  have b := fun x => hD x
  simp only [P_lit] at b
  have := b (jo 1); have := b (jo 2); have := b (jo 3); have := b (jo 4)
  nev_simp at f1 f2 f3 f4
  simp only [hvb, hpl] at f1 f2 f3 f4
  simp at f1 f2 f3 f4
  omega

/-- At the end of a part below the root part: `jo` shifts, `rc` drops by a descend, `cN` is
the source record. -/
theorem partEnd (hqb : C qb = 1) (hpl : C pl = 1) (hr : C rootP = 0) :
    D (jo 1) = 0 ∧ D (jo 2) = C (jo 1) ∧ D (jo 3) = C (jo 2) ∧ D (jo 4) = C (jo 3) ∧
    (D rc + C kRDB + C kRDE) % P = C rc ∧ D cN = C sN := by
  have g : ∀ x, x ∈ [rc, cN] ∨ True → True := fun _ _ => trivial
  have f1 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (n (jo 1))) (memRows (by simp [cRows]))
  have f2 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n (jo 2)) (c (jo 1))))
    (memRows (by simp [cRows]))
  have f3 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n (jo 3)) (c (jo 2))))
    (memRows (by simp [cRows]))
  have f4 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n (jo 4)) (c (jo 3))))
    (memRows (by simp [cRows]))
  have f5 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n rc) (sub (c rc) kRD)))
    (memRows (by simp [cRows]))
  have f6 := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (not (c rootP))) (sub (n cN) (c sN)))
    (memRows (by simp [cRows]))
  have b := fun x => hD x
  have a := fun x => hC x
  simp only [P_lit] at a b ⊢
  have := b (jo 1); have := b (jo 2); have := b (jo 3); have := b (jo 4); have := b rc; have := b cN
  have := a (jo 1); have := a (jo 2); have := a (jo 3); have := a rc; have := a sN; have := a kRDB; have := a kRDE
  simp only [kRD] at f5
  nev_simp at f1 f2 f3 f4 f5 f6
  simp only [hqb, hpl, hr] at f1 f2 f3 f4 f5 f6
  simp at f1 f2 f3 f4 f5 f6
  omega

/-- At the end of the root part: every descend counted. -/
theorem rootEnd (hqb : C qb = 1) (hpl : C pl = 1) (hr : C rootP = 1) :
    C rc = (C kRDB + C kRDE) % P := by
  have f := factN ok hC hD (e := .mul (mul3 (c qb) (c pl) (c rootP)) (sub (c rc) kRD)) (memRows (by simp [cRows]))
  have a := fun x => hC x
  simp only [P_lit] at a ⊢
  have := a rc; have := a kRDB; have := a kRDE
  simp only [kRD] at f
  nev_simp at f
  simp only [hqb, hpl, hr] at f
  simp at f
  omega

/-- The root part: depth `0`, number `nQ`, length `rlen`. -/
theorem rootPart (hqb : C qb = 1) (hr : C rootP = 1) : C pdep = 0 ∧ C j = C nQ ∧ C qlen = C rlen := by
  have f1 := factN ok hC hD (e := mul3 (c qb) (c rootP) (c pdep)) (memRows (by simp [cRows]))
  have f2 := factN ok hC hD (e := .mul (c qb) (.mul (c rootP) (sub (c j) (c nQ)))) (memRows (by simp [cRows]))
  have f3 := factN ok hC hD (e := .mul (c qb) (.mul (c rootP) (sub (c qlen) (c rlen)))) (memRows (by simp [cRows]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a pdep; have := a j; have := a nQ; have := a qlen; have := a rlen
  nev_simp at f1 f2 f3
  simp only [hqb, hr] at f1 f2 f3
  simp at f1 f2 f3
  omega

/-- `W0`: the number of parts. -/
theorem segNQ {ci ti di : Nat} (h1 : ci < 11) (h2 : ti < 3) (h3 : di < 3) (hsf : C sf = 1)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0)
    (hdd : ∀ m, m < 3 → C (28 + m) = if m = di then 1 else 0) :
    C nQ = (nTof ci ti + C (176 + di)) % P := by
  have eT := nTE_val (D := D) h1 h2 hcs hti
  have edep := nev_depDE ok hC hD h3 hdd
  have f := factN ok hC hD (e := .mul (c sf) (sub (c nQ) (.add nTE depDE))) (memSeg (by simp [cSeg]))
  simp only [nev, Dsl.sub, Dsl.k, Dsl.c, ite_false, Bool.false_eq_true, eT, edep, hsf, P_lit] at f
  have a := fun x => hC x
  simp only [P_lit] at a ⊢
  have := a nQ; have := a (176 + di); have := nTof_le ci h1 ti h2
  simp at f
  omega

end

end ZkFormal.NearV3.UpsRows
