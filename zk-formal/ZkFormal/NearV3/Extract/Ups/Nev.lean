import ZkFormal.NearV3.Extract.Ups.Rows

/-!
# ZkFormal.NearV3.Extract.Ups.Nev — constraints as natural-number facts

`nev C D e` evaluates a pure expression on canonical cells with natural-number arithmetic
modulo `P` (`(uev C D e).toNat = nev C D e`, `uev_toNat`).  So a vanishing constraint gives
`nev C D e = 0` (`factN`), which `simp` (with the known cell values) and `omega` (linear facts
modulo the literal `P`) turn into natural-number facts; and on rows whose relevant cells are
fixed by a few indices, `decide` checks the consequences of a constraint over all index
combinations (`nev_congr`).
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- Natural-number evaluation modulo `P` (cells are taken as they are: canonical rows). -/
def nev (C D : URow) : Expr → Nat
  | .const v => v % P
  | .col x nx => if nx then D x else C x
  | .add a b => (nev C D a + nev C D b) % P
  | .mul a b => (nev C D a * nev C D b) % P
  | .neg a => (P - nev C D a) % P
  | _ => 0

theorem uev_toNat {C D : URow} (hC : ∀ x, C x < P) (hD : ∀ x, D x < P) :
    ∀ e : Expr, e.pure = true → (uev C D e).toNat = nev C D e
  | .const v, _ => by
    show (Fp.ofNat v).toNat = v % P
    exact Fp.toNat_ofNat v
  | .col x nx, _ => by
    cases nx
    · show (Fp.ofNat (C x)).toNat = C x
      rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (hC x)]
    · show (Fp.ofNat (D x)).toNat = D x
      rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (hD x)]
  | .add a b, h => by
    simp only [Expr.pure, Bool.and_eq_true] at h
    show (uev C D a + uev C D b).toNat = _
    rw [Fp.add_def, Fp.toNat_add, uev_toNat hC hD a h.1, uev_toNat hC hD b h.2]; rfl
  | .mul a b, h => by
    simp only [Expr.pure, Bool.and_eq_true] at h
    show (uev C D a * uev C D b).toNat = _
    rw [Fp.mul_def, Fp.toNat_mul, uev_toNat hC hD a h.1, uev_toNat hC hD b h.2]; rfl
  | .neg a, h => by
    simp only [Expr.pure] at h
    show (-(uev C D a)).toNat = _
    rw [Fp.neg_def, Fp.toNat_neg, uev_toNat hC hD a h]; rfl
  | .pub _, h => by simp [Expr.pure] at h
  | .isFirst, h => by simp [Expr.pure] at h
  | .isLast, h => by simp [Expr.pure] at h
  | .isTransition, h => by simp [Expr.pure] at h

/-- A vanishing pure constraint, as a natural-number fact. -/
theorem factN {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P) {e : Expr}
    (hm : e ∈ UpsV3.constraints) (hp : e.pure = true := by rfl) : nev C D e = 0 := by
  rw [← uev_toNat hC hD e hp, ok e hm hp]; rfl

/-- Columns of the current row (`cs`) and of the next row (`ns`) that an expression reads. -/
def _root_.ZkFormal.Air.Expr.colsC : Expr → List Nat
  | .col x false => [x]
  | .add a b | .mul a b => a.colsC ++ b.colsC
  | .neg a => a.colsC
  | _ => []

def _root_.ZkFormal.Air.Expr.colsN : Expr → List Nat
  | .col x true => [x]
  | .add a b | .mul a b => a.colsN ++ b.colsN
  | .neg a => a.colsN
  | _ => []

theorem nev_congr {C D C' D' : URow} :
    ∀ e : Expr, (∀ x ∈ e.colsC, C x = C' x) → (∀ x ∈ e.colsN, D x = D' x) → nev C D e = nev C' D' e
  | .const _, _, _ => rfl
  | .col x nx, hc, hn => by
    cases nx
    · exact hc x (by simp [Expr.colsC])
    · exact hn x (by simp [Expr.colsN])
  | .add a b, hc, hn => by
    simp only [Expr.colsC, Expr.colsN, List.mem_append] at hc hn
    simp only [nev]
    rw [nev_congr a (fun x h => hc x (Or.inl h)) (fun x h => hn x (Or.inl h)),
      nev_congr b (fun x h => hc x (Or.inr h)) (fun x h => hn x (Or.inr h))]
  | .mul a b, hc, hn => by
    simp only [Expr.colsC, Expr.colsN, List.mem_append] at hc hn
    simp only [nev]
    rw [nev_congr a (fun x h => hc x (Or.inl h)) (fun x h => hn x (Or.inl h)),
      nev_congr b (fun x h => hc x (Or.inr h)) (fun x h => hn x (Or.inr h))]
  | .neg a, hc, hn => by
    simp only [Expr.colsC, Expr.colsN] at hc hn
    simp only [nev]
    rw [nev_congr a hc hn]
  | .pub _, _, _ => rfl
  | .isFirst, _, _ => rfl
  | .isLast, _, _ => rfl
  | .isTransition, _, _ => rfl

theorem P_lit : P = 2013265921 := rfl

/-- Unfold `nev` of a `Dsl` expression to nested `% P` arithmetic. -/
macro "nev_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [nev, Dsl.sub, Dsl.k, Dsl.c, Dsl.n, Dsl.not,
  Dsl.mul3, Dsl.sum, Dsl.smul, Dsl.bool, Dsl.bits, Dsl.mid, ite_true, ite_false, Bool.false_eq_true, P_lit] $[$loc]?)

end ZkFormal.NearV3.UpsRows
