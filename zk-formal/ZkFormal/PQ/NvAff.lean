import ZkFormal.PQ.NvTape

/-!
# ZkFormal.PQ.NvAff — partial evaluation of exported constraints into affine forms

Lane E (E2E M11g, item 2), 2026-11-04.

On an ALU row whose op selectors are known (one-hot halves `(a, b)`, role flags fixed), most
exported NvAir constraints collapse to an **affine** relation among the remaining columns
(e.g. `P1 − (8b + a)·2^24 − rx − 256·ry − 65536·rz` for the B-field decode). `affEval` computes
that form from the exported expression with some columns fixed, and `affEval_sound` proves the
expression's value on any row agreeing with the fixing is the form's value. A form is compared
with an expected one by its constant and its coefficient on each listed variable (`Aff.Is`,
`aff_is_eval`). This identifies the semantics of a constraint, interaction count or message on
the program's rows by kernel evaluation of one (small) exported expression per case, not by
transcription.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvAff

open ZkFormal.Air ZkFormal.Algebra

/-- An affine form `c + Σ k·x_v` over variables `v = (column, next)`. -/
structure Aff where
  c : Fp
  vs : List ((Nat × Bool) × Fp)
  deriving DecidableEq

/-- Fixed column values (`none`: the column is a variable). -/
abbrev Fix := Nat → Bool → Option Fp

def Aff.scale (k : Fp) (a : Aff) : Aff :=
  if k = 0 then ⟨0, []⟩ else ⟨k * a.c, a.vs.map fun p => (p.1, k * p.2)⟩

/-- A fixed value or a variable `(c, nx)`. -/
def atom (fx : Fix) (c : Nat) (nx : Bool) : Aff :=
  match fx c nx with
  | some v => ⟨v, []⟩
  | none => ⟨0, [((c, nx), 1)]⟩

/-- **Partial evaluation.** Columns `c < 1000` are `(c, nx)`; the selectors are the pseudo-columns
`isFirst = (1000, false)`, `isLast = (1001, false)`, `isTransition = (1002, false)`, and public
value `i` is `(2000 + i, false)`. Products of
two non-constant forms fail (`none`), except that a product with a constant-zero factor is
zero. -/
def affEval (fx : Fix) : Expr → Option Aff
  | .const n => some ⟨(n : Fp), []⟩
  | .col c nx => if c < 1000 then some (atom fx c nx) else none
  | .pub i => some (atom fx (2000 + i) false)
  | .isFirst => some (atom fx 1000 false)
  | .isLast => some (atom fx 1001 false)
  | .isTransition => some (atom fx 1002 false)
  | .add a b => match affEval fx a, affEval fx b with
    | some x, some y => some ⟨x.c + y.c, x.vs ++ y.vs⟩
    | _, _ => none
  | .neg a => (affEval fx a).map fun x => Aff.scale (-1) x
  | .mul a b => match affEval fx a, affEval fx b with
    | some x, some y =>
      if x.vs.isEmpty then some (Aff.scale x.c y)
      else if y.vs.isEmpty then some (Aff.scale y.c x)
      else none
    | some x, none => if x.vs.isEmpty && x.c == 0 then some ⟨0, []⟩ else none
    | none, some y => if y.vs.isEmpty && y.c == 0 then some ⟨0, []⟩ else none
    | none, none => none

/-- `Σ k·val v`. -/
def sumV (val : Nat → Bool → Fp) : List ((Nat × Bool) × Fp) → Fp
  | [] => 0
  | p :: ps => p.2 * val p.1.1 p.1.2 + sumV val ps

def Aff.eval (val : Nat → Bool → Fp) (a : Aff) : Fp := a.c + sumV val a.vs

theorem sumV_append (val : Nat → Bool → Fp) (x y : List ((Nat × Bool) × Fp)) :
    sumV val (x ++ y) = sumV val x + sumV val y := by
  induction x with
  | nil => simp [sumV]; grind
  | cons p ps ih => simp only [List.cons_append, sumV, ih]; grind

theorem sumV_scale (val : Nat → Bool → Fp) (k : Fp) (x : List ((Nat × Bool) × Fp)) :
    sumV val (x.map fun p => (p.1, k * p.2)) = k * sumV val x := by
  induction x with
  | nil => simp [sumV]; grind
  | cons p ps ih => simp only [List.map_cons, sumV, ih]; grind

theorem scale_eval (val : Nat → Bool → Fp) (k : Fp) (a : Aff) :
    (Aff.scale k a).eval val = k * a.eval val := by
  unfold Aff.scale
  split
  · next h => subst h; simp only [Aff.eval, sumV]; grind
  · simp only [Aff.eval, sumV_scale]; grind

theorem sumV_nil_of (val : Nat → Bool → Fp) {x : List ((Nat × Bool) × Fp)} (h : x.isEmpty = true) :
    sumV val x = 0 := by
  cases x with
  | nil => rfl
  | cons _ _ => simp at h

/-- The value of variable `(c, nx)` in an environment (selectors at the pseudo-columns). -/
def envVal (env : Env Fp) (c : Nat) (nx : Bool) : Fp :=
  if c = 1000 then env.isFirst else if c = 1001 then env.isLast
  else if c = 1002 then env.isTransition else if 2000 ≤ c then env.pub (c - 2000) else env.col c nx

/-- The environment agrees with a fixing. -/
def Agrees (fx : Fix) (env : Env Fp) : Prop := ∀ c nx v, fx c nx = some v → envVal env c nx = v

theorem atom_eval (fx : Fix) (env : Env Fp) (hag : Agrees fx env) (c : Nat) (nx : Bool) :
    (atom fx c nx).eval (envVal env) = envVal env c nx := by
  unfold atom
  cases hc : fx c nx with
  | some v => simp only [Aff.eval, sumV, hag c nx v hc]; grind
  | none => simp only [Aff.eval, sumV]; grind

/-- **Soundness of the partial evaluation** (over any environment with the field's operations). -/
theorem affEval_sound (fx : Fix) (env : Env Fp)
    (hof : ∀ n, env.ofNat n = (n : Fp)) (hadd : ∀ x y, env.add x y = x + y)
    (hmul : ∀ x y, env.mul x y = x * y) (hneg : ∀ x, env.neg x = -x) (hag : Agrees fx env) :
    ∀ (e : Expr) (a : Aff), affEval fx e = some a → e.evalWith env = a.eval (envVal env)
  | .const n, a, h => by
    simp only [affEval, Option.some.injEq] at h; subst h
    simp [Expr.evalWith, Aff.eval, sumV, hof]; grind
  | .col c nx, a, h => by
    simp only [affEval] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h; subst h
      rw [atom_eval fx env hag]
      simp only [Expr.evalWith, envVal]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · simp at h
  | .pub i, a, h => by
    simp only [affEval, Option.some.injEq] at h; subst h
    rw [atom_eval fx env hag]
    simp only [Expr.evalWith, envVal]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
  | .isFirst, a, h => by
    simp only [affEval, Option.some.injEq] at h; subst h
    rw [atom_eval fx env hag]; simp [Expr.evalWith, envVal]
  | .isLast, a, h => by
    simp only [affEval, Option.some.injEq] at h; subst h
    rw [atom_eval fx env hag]; simp [Expr.evalWith, envVal]
  | .isTransition, a, h => by
    simp only [affEval, Option.some.injEq] at h; subst h
    rw [atom_eval fx env hag]; simp [Expr.evalWith, envVal]
  | .add x y, a, h => by
    simp only [affEval] at h
    cases hx : affEval fx x with
    | none => rw [hx] at h; simp at h
    | some ax =>
      cases hy : affEval fx y with
      | none => rw [hx, hy] at h; simp at h
      | some ay =>
        rw [hx, hy] at h; simp only [Option.some.injEq] at h; subst h
        have ex := affEval_sound fx env hof hadd hmul hneg hag x ax hx
        have ey := affEval_sound fx env hof hadd hmul hneg hag y ay hy
        simp only [Expr.evalWith, hadd, ex, ey, Aff.eval, sumV_append]; grind
  | .neg x, a, h => by
    simp only [affEval] at h
    cases hx : affEval fx x with
    | none => rw [hx] at h; simp at h
    | some ax =>
      rw [hx] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have ex := affEval_sound fx env hof hadd hmul hneg hag x ax hx
      simp only [Expr.evalWith, hneg, ex, scale_eval]; grind
  | .mul x y, a, h => by
    simp only [affEval] at h
    have ev : ∀ (ax : Aff), affEval fx x = some ax → x.evalWith env = ax.eval (envVal env) :=
      fun ax hx => affEval_sound fx env hof hadd hmul hneg hag x ax hx
    have ew : ∀ (ay : Aff), affEval fx y = some ay → y.evalWith env = ay.eval (envVal env) :=
      fun ay hy => affEval_sound fx env hof hadd hmul hneg hag y ay hy
    cases hx : affEval fx x with
    | none =>
      cases hy : affEval fx y with
      | none => rw [hx, hy] at h; simp at h
      | some ay =>
        rw [hx, hy] at h
        simp only at h
        split at h
        · next hz =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hz
          have e2 := ew ay hy
          rw [Aff.eval, sumV_nil_of _ hz.1, hz.2] at e2
          simp only [Expr.evalWith, hmul, e2, Aff.eval, sumV]; grind
        · simp at h
    | some ax =>
      cases hy : affEval fx y with
      | none =>
        rw [hx, hy] at h
        simp only at h
        split at h
        · next hz =>
          simp only [Option.some.injEq] at h; subst h
          simp only [Bool.and_eq_true, beq_iff_eq] at hz
          have e1 := ev ax hx
          rw [Aff.eval, sumV_nil_of _ hz.1, hz.2] at e1
          simp only [Expr.evalWith, hmul, e1, Aff.eval, sumV]; grind
        · simp at h
      | some ay =>
        rw [hx, hy] at h
        simp only at h
        have e1 := ev ax hx
        have e2 := ew ay hy
        split at h
        · next hz =>
          simp only [Option.some.injEq] at h; subst h
          rw [Aff.eval, sumV_nil_of _ hz] at e1
          simp only [Expr.evalWith, hmul, e1, e2, scale_eval]; grind
        · split at h
          · next _ hz =>
            simp only [Option.some.injEq] at h; subst h
            rw [Aff.eval, sumV_nil_of _ hz] at e2
            simp only [Expr.evalWith, hmul, e1, e2, scale_eval]; grind
          · simp at h

/-- The value of variable `(c, nx)` on row `r` of table `t`. -/
abbrev rowVal (tr : Trace Fp) (t r : Nat) (pub : List Fp) : Nat → Bool → Fp :=
  envVal (rowEnv tr t r pub)

/-- `affEval_sound` on a trace row. -/
theorem affEval_row (fx : Fix) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hag : Agrees fx (rowEnv tr t r pub)) (e : Expr) (a : Aff)
    (h : affEval fx e = some a) : e.eval tr t r pub = a.eval (rowVal tr t r pub) :=
  affEval_sound fx (rowEnv tr t r pub) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) hag e a h

theorem rowVal_col (tr : Trace Fp) (t r : Nat) (pub : List Fp) (c : Nat) (hc : c < 1000) :
    rowVal tr t r pub c false = tr.cell t r c := by
  simp only [rowVal, envVal]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

theorem rowVal_pub (tr : Trace Fp) (t r : Nat) (pub : List Fp) (i : Nat) :
    rowVal tr t r pub (2000 + i) false = pub.getD i 0 := by
  simp only [rowVal, envVal]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  show pub.getD (2000 + i - 2000) 0 = _
  rw [Nat.add_sub_cancel_left]

theorem rowVal_colN (tr : Trace Fp) (t r : Nat) (pub : List Fp) (c : Nat) (hc : c < 1000) :
    rowVal tr t r pub c true = tr.cell t ((r + 1) % tr.height t) c := by
  simp only [rowVal, envVal]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rfl

/-! ## Comparing forms by coefficients -/

/-- Coefficient of variable `v`. -/
def coef (vs : List ((Nat × Bool) × Fp)) (v : Nat × Bool) : Fp :=
  vs.foldr (fun p s => (if p.1 = v then p.2 else 0) + s) 0

/-- `a` is `c + Σ_i ks_i · x_{vars_i}`: same constant, the listed coefficients, and no other
variable. -/
def Aff.Is (a : Aff) (c : Fp) (vars : List (Nat × Bool)) (ks : List Fp) : Bool :=
  a.c == c && vars.Nodup && (a.vs.all fun p => vars.contains p.1) &&
    (vars.zip ks).all (fun q => coef a.vs q.1 == q.2) && vars.length == ks.length

def lin (val : Nat → Bool → Fp) : List (Nat × Bool) → List Fp → Fp
  | v :: vs, k :: ks => k * val v.1 v.2 + lin val vs ks
  | _, _ => 0

/-- `Σ_{v ∈ vars} f v`. -/
def sumOver (f : Nat × Bool → Fp) : List (Nat × Bool) → Fp
  | [] => 0
  | v :: vs => f v + sumOver f vs

theorem sumOver_add (f g : Nat × Bool → Fp) : ∀ vars : List (Nat × Bool),
    sumOver (fun v => f v + g v) vars = sumOver f vars + sumOver g vars
  | [] => by simp only [sumOver]; grind
  | v :: vs => by simp only [sumOver, sumOver_add f g vs]; grind

theorem sumOver_zero : ∀ vars : List (Nat × Bool), sumOver (fun _ => 0) vars = 0
  | [] => rfl
  | v :: vs => by simp only [sumOver, sumOver_zero vs]; grind

theorem sumOver_congr (f g : Nat × Bool → Fp) (h : ∀ v, f v = g v) :
    ∀ vars : List (Nat × Bool), sumOver f vars = sumOver g vars
  | [] => rfl
  | v :: vs => by simp only [sumOver, h v, sumOver_congr f g h vs]

theorem sum_onehot (val : Nat → Bool → Fp) (k : Fp) (w : Nat × Bool) :
    ∀ vars : List (Nat × Bool), vars.Nodup →
      sumOver (fun v => (if w = v then k else 0) * val v.1 v.2) vars =
        if w ∈ vars then k * val w.1 w.2 else 0
  | [], _ => by simp [sumOver]
  | v :: vars, hnd => by
    have hnd' := (List.nodup_cons.1 hnd)
    simp only [sumOver, sum_onehot val k w vars hnd'.2, List.mem_cons]
    by_cases h : w = v
    · subst h
      have : w ∉ vars := hnd'.1
      simp only [if_true, true_or, this, if_false]; grind
    · simp only [h, if_false, false_or]
      split <;> grind

theorem coef_cons (p : (Nat × Bool) × Fp) (ps : List ((Nat × Bool) × Fp)) (v : Nat × Bool) :
    coef (p :: ps) v = (if p.1 = v then p.2 else 0) + coef ps v := rfl

theorem sumV_coef (val : Nat → Bool → Fp) (vars : List (Nat × Bool)) (hnd : vars.Nodup) :
    ∀ vs : List ((Nat × Bool) × Fp), (∀ p ∈ vs, p.1 ∈ vars) →
      sumV val vs = sumOver (fun v => coef vs v * val v.1 v.2) vars
  | [], _ => by
    rw [sumOver_congr _ (fun _ => 0) (fun v => by show (0 : Fp) * _ = 0; grind), sumOver_zero]
    rfl
  | p :: ps, hc => by
    have ih := sumV_coef val vars hnd ps (fun q hq => hc q (List.mem_cons_of_mem _ hq))
    have hp := hc p List.mem_cons_self
    rw [sumOver_congr _ (fun v => (if p.1 = v then p.2 else 0) * val v.1 v.2 +
      coef ps v * val v.1 v.2) (fun v => by rw [coef_cons]; grind), sumOver_add,
      sum_onehot val p.2 p.1 vars hnd, if_pos hp, ← ih]
    rfl

theorem lin_eq (val : Nat → Bool → Fp) (vs : List ((Nat × Bool) × Fp)) :
    ∀ (vars : List (Nat × Bool)) (ks : List Fp), vars.length = ks.length →
      (vars.zip ks).all (fun q => coef vs q.1 == q.2) = true →
      sumOver (fun v => coef vs v * val v.1 v.2) vars = lin val vars ks
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | v :: vars, k :: ks, hl, hc => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [sumOver, lin, hc.1, lin_eq val vs vars ks (by simpa using hl) hc.2]

/-- **An `Is`-checked form evaluates to its expected linear expression.** -/
theorem aff_is_eval (a : Aff) (c : Fp) (vars : List (Nat × Bool)) (ks : List Fp)
    (h : a.Is c vars ks = true) (val : Nat → Bool → Fp) : a.eval val = c + lin val vars ks := by
  simp only [Aff.Is, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hc, hnd⟩, hcov⟩, hk⟩, hl⟩ := h
  have hc : a.c = c := by simpa using hc
  have hnd : vars.Nodup := by simpa using hnd
  have hcov : ∀ p ∈ a.vs, p.1 ∈ vars := by simpa using hcov
  have hl : vars.length = ks.length := by simpa using hl
  rw [Aff.eval, sumV_coef val vars hnd a.vs hcov, hc, lin_eq val a.vs vars ks hl hk]

/-- An expression checked to partially evaluate to an `Is`-form. -/
def EvalIs (fx : Fix) (e : Expr) (c : Fp) (vars : List (Nat × Bool))
    (ks : List Fp) : Bool :=
  match affEval fx e with
  | some a => a.Is c vars ks
  | none => false

theorem evalIs_row (fx : Fix) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hag : Agrees fx (rowEnv tr t r pub)) (e : Expr) (c : Fp) (vars : List (Nat × Bool))
    (ks : List Fp) (h : EvalIs fx e c vars ks = true) :
    e.eval tr t r pub = c + lin (rowVal tr t r pub) vars ks := by
  unfold EvalIs at h
  cases ha : affEval fx e with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    rw [affEval_row fx tr t r pub hag e a ha]
    exact aff_is_eval a c vars ks h _

#print axioms affEval_sound
#print axioms aff_is_eval
#print axioms evalIs_row

end ZkFormal.PQ.NvAff
