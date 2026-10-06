import ZkFormal.NearV3.Extract.Ups.Nev

/-!
# ZkFormal.NearV3.Extract.Ups.PlanDefs — the part plan: cases, kinds, the planned kinds

The case selector, the terminal position `I`, the kinds and the position flags `jo` as
indices (`UCase`, `UKind`); the planned kind of a part by its position (`termPlan`), checked
over all index combinations by `decide` on `nev`; the transitions of `jo`, `rc`, `cN` at
part boundaries.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Cases and kinds -/

/-- The upsert case (the one-hot selector `cLP … cESn1`, in this order). -/
inductive UCase | LP | BR | BV | BI | LSa | LSb | LSc | ESl0 | ESl1 | ESn0 | ESn1
  deriving DecidableEq, Repr, Inhabited

/-- The kind of a node part (`kRDB … kSPB`, `kPT`, in `kinds` order). -/
inductive UKind | RDB | RDE | RLP | RBR | RBV | RBI | MVL | MVE | NLF | WEX | SPB | PT
  deriving DecidableEq, Repr, Inhabited

def UCase.all : List UCase := [.LP, .BR, .BV, .BI, .LSa, .LSb, .LSc, .ESl0, .ESl1, .ESn0, .ESn1]
def UKind.all : List UKind := [.RDB, .RDE, .RLP, .RBR, .RBV, .RBI, .MVL, .MVE, .NLF, .WEX, .SPB, .PT]

def UCase.ix : UCase → Nat
  | .LP => 0 | .BR => 1 | .BV => 2 | .BI => 3 | .LSa => 4 | .LSb => 5 | .LSc => 6 | .ESl0 => 7
  | .ESl1 => 8 | .ESn0 => 9 | .ESn1 => 10
def UKind.ix : UKind → Nat
  | .RDB => 0 | .RDE => 1 | .RLP => 2 | .RBR => 3 | .RBV => 4 | .RBI => 5 | .MVL => 6 | .MVE => 7
  | .NLF => 8 | .WEX => 9 | .SPB => 10 | .PT => 11

def UCase.col (c : UCase) : Nat := 17 + c.ix
def UKind.col : UKind → Nat
  | .RDB => kRDB | .RDE => kRDE | .RLP => kRLP | .RBR => kRBR | .RBV => kRBV | .RBI => kRBI
  | .MVL => kMVL | .MVE => kMVE | .NLF => kNLF | .WEX => kWEX | .SPB => kSPB | .PT => kPT

/-- A split case (leaf or extension split). -/
def UCase.split : UCase → Bool
  | .LP | .BR | .BV | .BI => false
  | _ => true

/-- An upper (path) kind: descend or pass-through. -/
def UKind.upper : UKind → Bool
  | .RDB | .RDE | .PT => true
  | _ => false

/-- The terminal parts of a case, bottom-up, with the wrapping extension when `I ≥ 1`. -/
def termPlan (cs : UCase) (I : Nat) : List UKind :=
  (match cs with
    | .LP => [.RLP] | .BR => [.RBR] | .BV => [.RBV] | .BI => [.NLF, .RBI]
    | .LSa => [.NLF, .SPB] | .LSb => [.MVL, .SPB] | .LSc => [.MVL, .NLF, .SPB]
    | .ESl0 => [.MVE, .SPB] | .ESl1 => [.SPB] | .ESn0 => [.MVE, .NLF, .SPB] | .ESn1 => [.NLF, .SPB]) ++
  (if cs.split && 1 ≤ I then [.WEX] else [])

/-- Number of terminal parts by index (`UCase.all` order). -/
def nTof (ci ti : Nat) : Nat := (termPlan (UCase.all.getD ci .LP) ti).length

theorem nTof_le : ∀ ci, ci < 11 → ∀ ti, ti < 3 → nTof ci ti ≤ 4 := by decide

/-! ## One-hot columns as an index -/

theorem sum_zero_mem {C : URow} : ∀ (xs : List Nat), (xs.map C).sum = 0 → ∀ y ∈ xs, C y = 0
  | [], _, _, h => by simp at h
  | x :: xs, hs, y, hy => by
    simp only [List.map_cons, List.sum_cons] at hs
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · exact sum_zero_mem xs (by omega) y hy

theorem oneHot_ix {C : URow} : ∀ (xs : List Nat), (∀ x ∈ xs, C x ≤ 1) → (xs.map C).sum = 1 →
    ∃ i, i < xs.length ∧ ∀ m (hm : m < xs.length), C xs[m] = if m = i then 1 else 0
  | [], _, h => by simp at h
  | x :: xs, hb, hs => by
    simp only [List.map_cons, List.sum_cons] at hs
    have hx := hb x (by simp)
    rcases (show C x = 0 ∨ C x = 1 by omega) with h0 | h1
    · obtain ⟨i, hi, hall⟩ := oneHot_ix xs (fun y hy => hb y (by simp [hy])) (by omega)
      refine ⟨i + 1, by simp; omega, fun m hm => ?_⟩
      rcases m with _ | m
      · simp [h0]
      · simp only [List.getElem_cons_succ]
        rw [hall m (by simp at hm; omega)]
        simp
    · have hz : (xs.map C).sum = 0 := by omega
      refine ⟨0, by simp, fun m hm => ?_⟩
      rcases m with _ | m
      · simp [h1]
      · simp only [List.getElem_cons_succ]
        have hm' : m < xs.length := by simp at hm; omega
        have : C (xs[m]'hm') = 0 := sum_zero_mem xs hz _ (List.getElem_mem hm')
        rw [this]; simp

/-! ## The planned kind, by `decide` -/

/-- Kind column by index (`kinds` order). -/
def kcol (m : Nat) : Nat := if m < 11 then 50 + m else kPT

/-- A part's first row with the plan indices fixed: case `ci`, `I = ti`, position `jj`
(`0` for `j ≥ 5`), kind `ki`, upper flag `uu`. -/
def planRow (ci ti jj ki uu : Nat) : URow := fun x =>
  if x = pf ∨ x = qb then 1
  else if 17 ≤ x ∧ x < 28 then (if x - 17 = ci then 1 else 0)
  else if 34 ≤ x ∧ x < 37 then (if x - 34 = ti then 1 else 0)
  else if 61 ≤ x ∧ x < 65 then (if x - 60 = jj then 1 else 0)
  else if 50 ≤ x ∧ x < 61 then (if x - 50 = ki then 1 else 0)
  else if x = kPT then (if ki = 11 then 1 else 0)
  else if x = UpsV3.up then uu
  else 0

def zrow : URow := fun _ => 0

def eKC : Expr := .mul (c pf) (sub kindCode (sum [.mul (c (jo 1)) plan1, .mul (c (jo 2)) plan2,
      .mul (c (jo 3)) plan3, .mul (c (jo 4)) plan4]))
def eUT : Expr := .mul (c pf) (sub (.add (c UpsV3.up) termE) (c qb))
def eUK : Expr := .mul (c pf) (sub (c UpsV3.up) (sumc [kRDB, kRDE, kPT]))

/-- What the plan says about a part with these indices. -/
def planOk (ci ti jj ki uu : Nat) : Bool :=
  let cs := UCase.all.getD ci .LP
  let kd := UKind.all.getD ki .RDB
  let tp := termPlan cs ti
  if 1 ≤ jj ∧ jj ≤ tp.length then kd == tp.getD (jj - 1) .RDB && uu == 0
  else kd.upper && uu == 1

def planCheck : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti => (List.range 5).all fun jj =>
    (List.range 12).all fun ki => (List.range 2).all fun uu =>
      !(nev (planRow ci ti jj ki uu) zrow eKC == 0 && nev (planRow ci ti jj ki uu) zrow eUT == 0 &&
        nev (planRow ci ti jj ki uu) zrow eUK == 0) || planOk ci ti jj ki uu

theorem planCheck_ok : planCheck = true := by decide +kernel

theorem planDec {ci ti jj ki uu : Nat} (h1 : ci < 11) (h2 : ti < 3) (h3 : jj < 5) (h4 : ki < 12) (h5 : uu < 2)
    (e1 : nev (planRow ci ti jj ki uu) zrow eKC = 0) (e2 : nev (planRow ci ti jj ki uu) zrow eUT = 0)
    (e3 : nev (planRow ci ti jj ki uu) zrow eUK = 0) : planOk ci ti jj ki uu = true := by
  have h := planCheck_ok
  simp only [planCheck, List.all_eq_true, List.mem_range] at h
  have := h ci h1 ti h2 jj h3 ki h4 uu h5
  simp only [e1, e2, e3, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact this

/-- Number of terminal parts by `decide`: `nTE` on a plan row. -/
def nTCheck : Bool :=
  (List.range 11).all fun ci => (List.range 3).all fun ti =>
    nev (planRow ci ti 0 0 0) zrow nTE == nTof ci ti

theorem nTCheck_ok : nTCheck = true := by decide +kernel

theorem nTDec {ci ti : Nat} (h1 : ci < 11) (h2 : ti < 3) :
    nev (planRow ci ti 0 0 0) zrow nTE = nTof ci ti := by
  have h := nTCheck_ok
  simp only [nTCheck, List.all_eq_true, List.mem_range] at h
  simpa using h ci h1 ti h2

/-- The columns a plan row fixes. -/
def planCols : List Nat :=
  [pf, qb, UpsV3.up, kPT] ++ (List.range 11).map (17 + ·) ++ (List.range 3).map (34 + ·) ++
    (List.range 15).map (50 + ·)

theorem planCols_mem : ∀ x ∈ planCols,
    x = 8 ∨ x = 3 ∨ x = 180 ∨ x = 179 ∨ (17 ≤ x ∧ x < 28) ∨ (34 ≤ x ∧ x < 37) ∨ (50 ≤ x ∧ x < 65) := by
  decide

theorem pf_v : pf = 8 := rfl
theorem qb_v : qb = 3 := rfl
theorem up_v : UpsV3.up = 180 := rfl
theorem kPT_v : kPT = 179 := rfl

theorem planAgree {C : URow} {ci ti jj ki uu : Nat} (hpf : C pf = 1) (hqb : C qb = 1) (hup : C UpsV3.up = uu)
    (hcs : ∀ m, m < 11 → C (17 + m) = if m = ci then 1 else 0)
    (hti : ∀ m, m < 3 → C (34 + m) = if m = ti then 1 else 0)
    (hjo : ∀ m, m < 4 → C (61 + m) = if m + 1 = jj then 1 else 0)
    (hk : ∀ m, m < 12 → C (kcol m) = if m = ki then 1 else 0) :
    ∀ x ∈ planCols, C x = planRow ci ti jj ki uu x := by
  intro x hx
  have hx' := planCols_mem x hx
  unfold planRow
  by_cases a1 : x = pf ∨ x = qb
  · rw [if_pos a1]; rcases a1 with rfl | rfl
    · exact hpf
    · exact hqb
  rw [if_neg a1]
  rw [pf_v, qb_v] at a1
  by_cases a2 : 17 ≤ x ∧ x < 28
  · rw [if_pos a2]; have := hcs (x - 17) (by omega); rwa [show 17 + (x - 17) = x by omega] at this
  rw [if_neg a2]
  by_cases a3 : 34 ≤ x ∧ x < 37
  · rw [if_pos a3]; have := hti (x - 34) (by omega); rwa [show 34 + (x - 34) = x by omega] at this
  rw [if_neg a3]
  by_cases a4 : 61 ≤ x ∧ x < 65
  · rw [if_pos a4]; have := hjo (x - 61) (by omega); rw [show 61 + (x - 61) = x by omega] at this
    rw [this]; simp only [show (x - 61 + 1 = jj) ↔ (x - 60 = jj) by omega]
  rw [if_neg a4]
  by_cases a5 : 50 ≤ x ∧ x < 61
  · rw [if_pos a5]; have := hk (x - 50) (by omega)
    simp only [kcol, show x - 50 < 11 by omega, ite_true, show 50 + (x - 50) = x by omega] at this
    exact this
  rw [if_neg a5]
  by_cases a6 : x = kPT
  · rw [if_pos a6]; subst a6; have := hk 11 (by omega); simpa [kcol, eq_comm] using this
  rw [if_neg a6]
  rw [kPT_v] at a6
  by_cases a7 : x = UpsV3.up
  · rw [if_pos a7]; subst a7; exact hup
  · rw [up_v] at a7; omega

theorem eKC_cols : (∀ x ∈ eKC.colsC, x ∈ planCols) ∧ eKC.colsN = [] := by decide
theorem eUT_cols : (∀ x ∈ eUT.colsC, x ∈ planCols) ∧ eUT.colsN = [] := by decide
theorem eUK_cols : (∀ x ∈ eUK.colsC, x ∈ planCols) ∧ eUK.colsN = [] := by decide
theorem nTE_cols : (∀ x ∈ nTE.colsC, x ∈ planCols) ∧ nTE.colsN = [] := by decide

theorem nev_plan {C D : URow} {ci ti jj ki uu : Nat} (hag : ∀ x ∈ planCols, C x = planRow ci ti jj ki uu x)
    {e : Expr} (he : (∀ x ∈ e.colsC, x ∈ planCols) ∧ e.colsN = []) :
    nev C D e = nev (planRow ci ti jj ki uu) zrow e :=
  nev_congr e (fun x hx => hag x (he.1 x hx)) (by rw [he.2]; simp)

theorem nTE_sub : ∀ y ∈ nTE.colsC, (17 ≤ y ∧ y < 28) ∨ (34 ≤ y ∧ y < 37) := by decide

/-- `nTE` does not depend on `jj`, `ki`, `uu`. -/
theorem planRow_nTE (ci ti jj ki uu : Nat) :
    nev (planRow ci ti jj ki uu) zrow nTE = nev (planRow ci ti 0 0 0) zrow nTE := by
  apply nev_congr nTE _ (by rw [nTE_cols.2]; simp)
  intro x hx
  have := nTE_sub x hx
  unfold planRow
  have h1 : ¬ (x = pf ∨ x = qb) := by rw [pf_v, qb_v]; omega
  rw [if_neg h1, if_neg h1]
  rcases this with h | h
  · rw [if_pos h, if_pos h]
  · have h2 : ¬ (17 ≤ x ∧ x < 28) := by omega
    simp only [h2, h, ite_false, ite_true, and_self]

end ZkFormal.NearV3.UpsRows
