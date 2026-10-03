import ZkFormal.Algebra.Statements

/-!
# ZkFormal.Algebra.PolyLemmas — evaluation, coefficients, degrees, `quot`

Proves `PolyEvalStmt`, `PolyDegStmt`, `PolySizeStmt`, `IsZeroEvalStmt` and
`QuotStmt` from the definitions in `ZkFormal.Algebra.Poly`.  The individual
facts are exported as `Poly.*` lemmas generic over `[Lean.Grind.CommRing K]`:
list level (`evalL_addL`, `getD_mulL_of_degLt`, …) and polynomial level
(`eval_add`, `coeff_add`, `degLt_mul`, `eval_quot`, `degLt_quot`, …).
-/

namespace ZkFormal.Algebra

open Lean.Grind

namespace Poly

section Ring
variable {K : Type} [CommRing K]

/-! ## Structural simp lemmas -/

@[simp] theorem evalL_nil (x : K) : evalL x ([] : List K) = 0 := rfl
@[simp] theorem evalL_cons (x c : K) (cs : List K) : evalL x (c :: cs) = c + x * evalL x cs := rfl
@[simp] theorem addL_nil_left (g : List K) : addL [] g = g := rfl
@[simp] theorem addL_nil_right (f : List K) : addL f [] = f := by cases f <;> rfl
@[simp] theorem addL_cons_cons (a b : K) (f g : List K) :
    addL (a :: f) (b :: g) = (a + b) :: addL f g := rfl
@[simp] theorem scaleL_nil (c : K) : scaleL c ([] : List K) = [] := rfl
@[simp] theorem scaleL_cons (c a : K) (f : List K) : scaleL c (a :: f) = (c * a) :: scaleL c f := rfl
@[simp] theorem mulL_nil (g : List K) : mulL [] g = [] := rfl
@[simp] theorem mulL_cons (a : K) (f g : List K) :
    mulL (a :: f) g = addL (scaleL a g) (0 :: mulL f g) := rfl
@[simp] theorem quotL_nil (r : K) : quotL r ([] : List K) = [] := rfl
@[simp] theorem quotL_cons (r c : K) (g : List K) :
    quotL r (c :: g) = addL g (scaleL r (quotL r g)) := rfl

@[simp] theorem coeffs_add (f g : Poly K) : (f + g).coeffs = addL f.coeffs g.coeffs := rfl
@[simp] theorem coeffs_mul (f g : Poly K) : (f * g).coeffs = mulL f.coeffs g.coeffs := rfl
@[simp] theorem coeffs_neg (f : Poly K) : (-f).coeffs = scaleL (-1) f.coeffs := rfl
theorem sub_def (f g : Poly K) : f - g = f + -g := rfl
@[simp] theorem coeffs_sub (f g : Poly K) :
    (f - g).coeffs = addL f.coeffs (scaleL (-1) g.coeffs) := rfl
@[simp] theorem coeffs_smul (c : K) (f : Poly K) : (smul c f).coeffs = scaleL c f.coeffs := rfl
omit [CommRing K] in
@[simp] theorem coeffs_zero : (zero : Poly K).coeffs = [] := rfl
omit [CommRing K] in
@[simp] theorem coeffs_C (c : K) : (C c).coeffs = [c] := rfl
@[simp] theorem coeffs_X : (X : Poly K).coeffs = [0, 1] := rfl
@[simp] theorem coeffs_quot (f : Poly K) (r : K) : (f.quot r).coeffs = quotL r f.coeffs := rfl
theorem eval_def (f : Poly K) (x : K) : f.eval x = evalL x f.coeffs := rfl
theorem coeff_def (f : Poly K) (i : Nat) : f.coeff i = f.coeffs.getD i 0 := rfl

/-! ## Evaluation (list level) -/

theorem evalL_addL (x : K) : ∀ f g : List K, evalL x (addL f g) = evalL x f + evalL x g
  | [], g => by simp; grind
  | a :: f, [] => by simp; grind
  | a :: f, b :: g => by simp [evalL_addL x f g]; grind

theorem evalL_scaleL (x c : K) : ∀ f : List K, evalL x (scaleL c f) = c * evalL x f
  | [] => by simp; grind
  | a :: f => by simp [evalL_scaleL x c f]; grind

theorem evalL_mulL (x : K) : ∀ f g : List K, evalL x (mulL f g) = evalL x f * evalL x g
  | [], g => by simp; grind
  | a :: f, g => by simp [evalL_addL, evalL_scaleL, evalL_mulL x f g]; grind

theorem evalL_quotL (r x : K) : ∀ f : List K,
    evalL x f - evalL r f = (x - r) * evalL x (quotL r f)
  | [] => by simp; grind
  | c :: g => by
    have ih := evalL_quotL r x g
    simp [evalL_addL, evalL_scaleL]; grind

/-! ## Evaluation (polynomial level) -/

theorem eval_add (f g : Poly K) (x : K) : (f + g).eval x = f.eval x + g.eval x :=
  evalL_addL x _ _
theorem eval_mul (f g : Poly K) (x : K) : (f * g).eval x = f.eval x * g.eval x :=
  evalL_mulL x _ _
theorem eval_smul (c : K) (f : Poly K) (x : K) : (smul c f).eval x = c * f.eval x :=
  evalL_scaleL x c _
theorem eval_neg (f : Poly K) (x : K) : (-f).eval x = -f.eval x := by
  show evalL x (scaleL (-1) f.coeffs) = _
  rw [evalL_scaleL, eval_def]; grind
theorem eval_sub (f g : Poly K) (x : K) : (f - g).eval x = f.eval x - g.eval x := by
  rw [sub_def, eval_add, eval_neg]; grind
@[simp] theorem eval_C (c x : K) : (C c).eval x = c := by
  show c + x * 0 = c; grind
@[simp] theorem eval_X (x : K) : (X : Poly K).eval x = x := by
  show (0 : K) + x * (1 + x * 0) = x; grind
@[simp] theorem eval_zero (x : K) : (zero : Poly K).eval x = 0 := rfl
/-- Factor theorem: `f(x) − f(r) = (x − r)·(quot f r)(x)`. -/
theorem eval_quot (f : Poly K) (r x : K) : f.eval x - f.eval r = (x - r) * (f.quot r).eval x :=
  evalL_quotL r x _

/-! ## Coefficients (list level) -/

theorem getD_addL : ∀ (f g : List K) (i : Nat),
    (addL f g).getD i 0 = f.getD i 0 + g.getD i 0
  | [], g, i => by simp; grind
  | a :: f, [], i => by simp; grind
  | a :: f, b :: g, 0 => by simp
  | a :: f, b :: g, i + 1 => by
    rw [addL_cons_cons, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_addL f g i

theorem getD_scaleL (c : K) : ∀ (f : List K) (i : Nat), (scaleL c f).getD i 0 = c * f.getD i 0
  | [], i => by simp; grind
  | a :: f, 0 => by simp
  | a :: f, i + 1 => by
    rw [scaleL_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_scaleL c f i

theorem getD_cons_zero_left (l : List K) : ∀ i : Nat,
    (0 :: l).getD i 0 = if i = 0 then 0 else l.getD (i - 1) 0
  | 0 => by simp
  | i + 1 => by simp

theorem getD_ge_length : ∀ (f : List K) (i : Nat), f.length ≤ i → f.getD i 0 = 0
  | [], i, _ => by simp
  | a :: f, 0, h => by simp at h
  | a :: f, i + 1, h => by
    simp at h
    rw [List.getD_cons_succ]
    exact getD_ge_length f i (by omega)

/-- List-level `DegLt`. -/
def DegLtL (l : List K) (D : Nat) : Prop := ∀ i, D ≤ i → l.getD i 0 = 0

theorem degLtL_cons_succ (a : K) (f : List K) (D : Nat) :
    DegLtL (a :: f) (D + 1) ↔ DegLtL f D := by
  constructor
  · intro h i hi; have := h (i + 1) (by omega); simpa using this
  · intro h i hi
    cases i with
    | zero => omega
    | succ i => simpa using h i (by omega)

theorem degLtL_cons_zero (a : K) (f : List K) :
    DegLtL (a :: f) 0 ↔ a = 0 ∧ DegLtL f 0 := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun i _ => by simpa using h (i + 1) (by omega)⟩
  · rintro ⟨ha, h⟩ i _
    cases i with
    | zero => simpa using ha
    | succ i => simpa using h i (by omega)

theorem DegLtL.mono {l : List K} {a b : Nat} (h : DegLtL l a) (hab : a ≤ b) : DegLtL l b :=
  fun i hi => h i (by omega)

theorem getD_mulL_of_zero : ∀ (f g : List K), DegLtL f 0 → DegLtL (mulL f g) 0
  | [], g, _ => by intro i _; simp
  | a :: f, g, h => by
    rw [degLtL_cons_zero] at h
    obtain ⟨ha, hf⟩ := h
    have ih := getD_mulL_of_zero f g hf
    intro i _
    rw [mulL_cons, getD_addL, getD_scaleL, getD_cons_zero_left, ha]
    split
    · grind
    · rw [ih _ (Nat.zero_le _)]; grind

theorem degLtL_mulL : ∀ (f g : List K) (a b : Nat), DegLtL f (a + 1) → DegLtL g (b + 1) →
    DegLtL (mulL f g) (a + b + 1)
  | [], g, a, b, _, _ => by intro i _; simp
  | c :: f, g, a, b, hf, hg => by
    rw [degLtL_cons_succ] at hf
    intro i hi
    rw [mulL_cons, getD_addL, getD_scaleL, getD_cons_zero_left, hg i (by omega)]
    split
    · grind
    · cases a with
      | zero =>
        rw [getD_mulL_of_zero f g hf _ (Nat.zero_le _)]; grind
      | succ a =>
        rw [degLtL_mulL f g a b hf hg (i - 1) (by omega)]; grind

theorem degLtL_addL {f g : List K} {D : Nat} (hf : DegLtL f D) (hg : DegLtL g D) :
    DegLtL (addL f g) D := by
  intro i hi; rw [getD_addL, hf i hi, hg i hi]; grind

theorem degLtL_scaleL (c : K) {f : List K} {D : Nat} (hf : DegLtL f D) :
    DegLtL (scaleL c f) D := by
  intro i hi; rw [getD_scaleL, hf i hi]; grind

theorem degLtL_quotL (r : K) : ∀ (f : List K) (D : Nat), DegLtL f (D + 1) → DegLtL (quotL r f) D
  | [], D, _ => by intro i _; simp
  | c :: g, D, h => by
    rw [degLtL_cons_succ] at h
    have ih := degLtL_quotL r g D (h.mono (by omega))
    exact degLtL_addL h (degLtL_scaleL r ih)

/-! ## Coefficients and degrees (polynomial level) -/

theorem coeff_add (f g : Poly K) (i : Nat) : (f + g).coeff i = f.coeff i + g.coeff i :=
  getD_addL _ _ _
theorem coeff_smul (c : K) (f : Poly K) (i : Nat) : (smul c f).coeff i = c * f.coeff i :=
  getD_scaleL _ _ _
theorem coeff_neg (f : Poly K) (i : Nat) : (-f).coeff i = -f.coeff i := by
  show (scaleL (-1) f.coeffs).getD i 0 = _
  rw [getD_scaleL]; show -1 * f.coeff i = _; grind
theorem coeff_sub (f g : Poly K) (i : Nat) : (f - g).coeff i = f.coeff i - g.coeff i := by
  rw [sub_def, coeff_add, coeff_neg]; grind

theorem degLt_iff_degLtL (f : Poly K) (D : Nat) : f.DegLt D ↔ DegLtL f.coeffs D := Iff.rfl

theorem degLt_length (f : Poly K) : f.DegLt f.coeffs.length :=
  fun _ hi => getD_ge_length _ _ hi
theorem DegLt.mono {f : Poly K} {a b : Nat} (h : f.DegLt a) (hab : a ≤ b) : f.DegLt b :=
  DegLtL.mono h hab
theorem degLt_add {f g : Poly K} {D : Nat} (hf : f.DegLt D) (hg : g.DegLt D) :
    (f + g).DegLt D := degLtL_addL hf hg
theorem degLt_smul (c : K) {f : Poly K} {D : Nat} (hf : f.DegLt D) : (smul c f).DegLt D :=
  degLtL_scaleL c hf
theorem degLt_neg {f : Poly K} {D : Nat} (hf : f.DegLt D) : (-f).DegLt D :=
  degLtL_scaleL (-1) hf
theorem degLt_sub {f g : Poly K} {D : Nat} (hf : f.DegLt D) (hg : g.DegLt D) :
    (f - g).DegLt D := degLt_add hf (degLt_neg hg)
theorem degLt_mul {f g : Poly K} {a b : Nat} (hf : f.DegLt (a + 1)) (hg : g.DegLt (b + 1)) :
    (f * g).DegLt (a + b + 1) := degLtL_mulL _ _ a b hf hg
/-- Dividing by `X − r` lowers the degree bound by one. -/
theorem degLt_quot (f : Poly K) (r : K) {D : Nat} (hf : f.DegLt (D + 1)) :
    (f.quot r).DegLt D := degLtL_quotL r _ D hf

/-! ## Zero polynomials -/

theorem evalL_of_degLtL_zero (x : K) : ∀ f : List K, DegLtL f 0 → evalL x f = 0
  | [], _ => rfl
  | a :: f, h => by
    rw [degLtL_cons_zero] at h
    rw [evalL_cons, h.1, evalL_of_degLtL_zero x f h.2]; grind

theorem isZero_iff_degLt_zero (f : Poly K) : f.IsZero ↔ f.DegLt 0 :=
  ⟨fun h i _ => h i, fun h i => h i (Nat.zero_le _)⟩

theorem eval_of_isZero {f : Poly K} (h : f.IsZero) (x : K) : f.eval x = 0 :=
  evalL_of_degLtL_zero x _ (fun i _ => h i)

/-! ## `size` -/

section Size
variable [DecidableEq K]

theorem trimL_cons (a : K) (f : List K) :
    trimL (a :: f) = if trimL f = [] ∧ a = 0 then [] else a :: trimL f := by
  unfold trimL
  rw [List.reverse_cons, List.dropWhile_append]
  by_cases h : (List.dropWhile (fun x => decide (x = 0)) f.reverse) = []
  · simp only [h, List.isEmpty_nil, ite_true, List.reverse_nil, true_and]
    by_cases ha : a = 0
    · simp [List.dropWhile, ha]
    · simp [List.dropWhile, ha]
  · have h' : (List.dropWhile (fun x => decide (x = 0)) f.reverse).isEmpty = false := by
      cases hh : List.dropWhile (fun x => decide (x = 0)) f.reverse with
      | nil => exact absurd hh h
      | cons _ _ => rfl
    rw [h', ite_eq_right (by simp)]
    have h2 : ¬ (List.dropWhile (fun x => decide (x = 0)) f.reverse).reverse = [] := by
      simpa using h
    rw [ite_eq_right (by simp [h2])]
    simp

theorem degLtL_iff_length_trimL : ∀ (f : List K) (D : Nat), DegLtL f D ↔ (trimL f).length ≤ D
  | [], D => by
    constructor
    · intro _; simp [trimL]
    · intro _ i _; simp
  | a :: f, D => by
    have ih0 := degLtL_iff_length_trimL f 0
    have hz : DegLtL f 0 ↔ trimL f = [] := by
      rw [ih0]; simp
    rw [trimL_cons]
    cases D with
    | zero =>
      rw [degLtL_cons_zero, hz]
      by_cases h : trimL f = [] ∧ a = 0
      · rw [ite_eq_left h]; simp [h.1, h.2]
      · rw [ite_eq_right h]; simp only [List.length_cons]
        constructor
        · rintro ⟨h1, h2⟩; exact absurd ⟨h2, h1⟩ h
        · intro hh; omega
    | succ D =>
      rw [degLtL_cons_succ, degLtL_iff_length_trimL f D]
      by_cases h : trimL f = [] ∧ a = 0
      · rw [ite_eq_left h, h.1]; simp
      · rw [ite_eq_right h]; simp

theorem degLt_iff_size_le (f : Poly K) (D : Nat) : f.DegLt D ↔ f.size ≤ D :=
  degLtL_iff_length_trimL _ _

end Size

end Ring

end Poly

/-! ## The `Statements` obligations -/

open Poly in
theorem polyEval : PolyEvalStmt := by
  intro K _ f g x c
  exact ⟨eval_add f g x, eval_mul f g x, eval_neg f x, eval_sub f g x, eval_smul c f x,
    eval_C c x, eval_X x, eval_zero x⟩

open Poly in
theorem polyDeg : PolyDegStmt := by
  intro K _ f g c a b
  exact ⟨coeff_add f g, coeff_smul c f, degLt_length f, fun h hab => h.mono hab,
    degLt_add, degLt_smul c, degLt_neg, degLt_mul⟩

theorem polySize : PolySizeStmt := by
  intro K _ _ f D
  exact Poly.degLt_iff_size_le f D

theorem isZeroEval : IsZeroEvalStmt := by
  intro K _ f x h
  exact Poly.eval_of_isZero h x

theorem quotFacts : QuotStmt := by
  intro K _ f r x D
  exact ⟨Poly.eval_quot f r x, Poly.degLt_quot f r⟩

end ZkFormal.Algebra
