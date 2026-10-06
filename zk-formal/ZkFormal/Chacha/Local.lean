import ZkFormal.Chacha.ZEval
import ZkFormal.Sha.Eval

/-!
# ZkFormal.Chacha.Local — local facts for any table given by its constraint list

`Local cs tr t pub`: every expression of `cs` vanishes on every row of table `t`.
Used by the stream (`genV3`) and shuffle (`shufV3`) tables.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table

def Local (cs : List Expr) (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height t → ∀ e ∈ cs, e.eval tr t r pub = 0

/-- Cell as a natural. -/
def cv (tr : Trace Fp) (t r c : Nat) : Nat := (tr.cell t r c).toNat

variable {cs : List Expr} {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem cur_cv (r x : Nat) : (tenv tr t r pub).cur x = cv tr t r x := rfl

theorem nxt_cv {r : Nat} (hr : r + 1 < tr.height t) (x : Nat) :
    (tenv tr t r pub).nxt x = cv tr t (r + 1) x := by
  show (tr.cell t ((r + 1) % tr.height t) x).toNat = _
  rw [Nat.mod_eq_of_lt hr]; rfl

theorem cv_lt (r x : Nat) : cv tr t r x < 2013265921 := (tr.cell t r x).toNat_lt

theorem Local.zc (hL : Local cs tr t pub) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ cs) (h1 : -2013265921 < zev (tenv tr t r pub) e)
    (h2 : zev (tenv tr t r pub) e < 2013265921) : zev (tenv tr t r pub) e = 0 :=
  zev_eq_zero (hL r hr e he) h1 h2

theorem Local.bool (hL : Local cs tr t pub) {r : Nat} (hr : r < tr.height t) {x : Nat}
    (hx : boolC x ∈ cs) : cv tr t r x ≤ 1 := by
  have h := hL r hr (boolC x) hx
  have h' : Fp.mul (tr.cell t r x) (Fp.add (tr.cell t r x) (Fp.neg (Fp.ofNat 1))) = 0 := h
  rcases ZkFormal.Sha.fp_mul_eq_zero h' with h0 | h1
  · unfold cv; rw [h0]; decide
  · have : tr.cell t r x = Fp.ofNat 1 := by
      have e := congrArg (fun z => Fp.add z (Fp.ofNat 1)) h1
      apply Fp.ext
      have h3 := congrArg Fp.toNat e
      simp only [Fp.toNat_add, Fp.toNat_neg, Fp.toNat_ofNat] at h3
      have := (tr.cell t r x).toNat_lt
      rw [show (0 : Fp) = Fp.ofNat 0 from rfl, Fp.toNat_ofNat] at h3
      rw [Fp.toNat_ofNat]
      unfold P at *
      omega
    unfold cv; rw [this]; decide

/-- `Σ_{b<len} 2^b · cv (col b)`. -/
def numv (tr : Trace Fp) (t r : Nat) (col : Nat → Nat) (len : Nat) : Nat :=
  nbits (fun b => cv tr t r (col b)) len

theorem zev_sum_pow (Z : ZEnv) (f : Nat → Expr) (g : Nat → Nat) (len : Nat)
    (h : ∀ b, b < len → zev Z (f b) = (g b : Int)) :
    zev Z (E.sum ((List.range len).map fun b => E.smul (2 ^ b) (f b))) = (nbits g len : Int) := by
  rw [zev_sum, List.map_map]
  induction len with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih (fun b hb => h b (by omega))]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Function.comp,
      zev_smul, nbits, h m (by omega)]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow, Int.add_zero]

theorem nbits_le_of {f : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b ≤ 1) : nbits f n < 2 ^ n :=
  nbits_lt h

end ZkFormal.Chacha
