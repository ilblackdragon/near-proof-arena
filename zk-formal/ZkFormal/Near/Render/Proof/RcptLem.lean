import ZkFormal.Near.Render.Proof.RcptStr

/-!
# ZkFormal.Near.Render.Proof.RcptLem — arithmetic toolkit for the `rcpt` rows

* `Fp.ofNat` of `x % P`, of `sqd`, of a truncated difference, inverses `invP`;
* bit pools: `bitsX off len` of the bits of `x < 2^len` is `x` (`evR_bitsX_of`);
* `evR_congr`: an expression only depends on the cells it reads (`colsC`,
  `colsN`), so a row can be replaced by a synthetic one.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-! ## `Fp` -/

theorem P_def : Render.P = ZkFormal.Algebra.P := rfl

theorem ofNat_mod (x : Nat) : Fp.ofNat (x % P) = Fp.ofNat x := by
  apply Fp.ext; simp [Fp.toNat_ofNat, Nat.mod_mod, P_def]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) : Fp.ofNat (a - b) = Fp.ofNat a - Fp.ofNat b := by
  have : Fp.ofNat a = Fp.ofNat (a - b) + Fp.ofNat b := by rw [ofNat_add']; congr 1; omega
  rw [this]; grind

theorem ofNat_sqd (a b : Nat) : Fp.ofNat (sqd a b) = (Fp.ofNat a - Fp.ofNat b) * (Fp.ofNat a - Fp.ofNat b) := by
  unfold sqd
  rcases Nat.le_total b a with h | h
  · rw [show b - a = 0 by omega, Nat.zero_mul, Nat.add_zero, ← ofNat_mul', ofNat_sub h]
  · rw [show a - b = 0 by omega, Nat.zero_mul, Nat.zero_add, ← ofNat_mul', ofNat_sub h]; grind

theorem ofNat_ne_zero {x : Nat} (h1 : x ≠ 0) (h2 : x < P) : Fp.ofNat x ≠ 0 := by
  intro h
  have := congrArg Fp.toNat h
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← P_def]; exact h2)] at this
  exact h1 (this.trans rfl)

theorem ofNat_invP {x : Nat} (h : Fp.ofNat x ≠ 0) : Fp.ofNat x * Fp.ofNat (invP x) = 1 := by
  simp only [invP, Fp.ofNat_toNat]
  exact Fp.mul_inv_cancel h

theorem ofNat_lt_eq {x : Nat} (h : x < P) : (Fp.ofNat x).toNat = x := by
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← P_def]; exact h)]

/-! ## Bits -/

theorem bitOf_le (x j : Nat) : bitOf x j ≤ 1 := by unfold bitOf; omega

theorem bitsVal_bitOf (x : Nat) : ∀ len, bitsVal (fun j => bitOf x j) 0 len = x % 2 ^ len
  | 0 => by simp [bitsVal, Nat.mod_one]
  | len + 1 => by
    rw [bitsVal, bitsVal_bitOf x len, Nat.zero_add, bitOf, Nat.pow_succ, Nat.mod_mul]

theorem bitsVal_congr {v w : Nat → Nat} (off : Nat) : ∀ len, (∀ j, j < len → v (off + j) = w j) →
    bitsVal v off len = bitsVal w 0 len
  | 0, _ => rfl
  | len + 1, h => by
    rw [bitsVal, bitsVal, bitsVal_congr off len (fun j hj => h j (by omega)), h len (by omega), Nat.zero_add]

theorem evR_bitsX {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {v : Nat → Nat} (off : Nat) :
    ∀ len, (∀ j, off ≤ j → j < off + len → cur (Rcpt.xb j) = Fp.ofNat (v j)) →
      evR cur nx fst lst pub (Rcpt.bitsX off len) = Fp.ofNat (bitsVal v off len)
  | 0, _ => rfl
  | len + 1, hv => by
    rw [Rcpt.bitsX, bits_succ]
    have h := evR_bitsX (nx := nx) (fst := fst) (lst := lst) (pub := pub) off len (fun j h1 h2 => hv j h1 (by omega))
    have hv := hv (off + len) (by omega) (by omega)
    rw [Rcpt.bitsX, bits] at h
    have e : ∀ (l1 l2 : List Expr), evR cur nx fst lst pub (sum (l1 ++ l2)) =
        evR cur nx fst lst pub (sum l1) + evR cur nx fst lst pub (sum l2) := by
      intro l1 l2; induction l1 with
      | nil => simp; grind
      | cons a l ih => simp [ih]; grind
    rw [e, h]
    simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_c, hv, bitsVal, natCast_eq, ofNat_add_e, ofNat_mul_e]
    grind

theorem evR_bitsXn {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {v : Nat → Nat} (off : Nat) :
    ∀ len, (∀ j, off ≤ j → j < off + len → nx (Rcpt.xb j) = Fp.ofNat (v j)) →
      evR cur nx fst lst pub (Rcpt.bitsXn off len) = Fp.ofNat (bitsVal v off len)
  | 0, _ => rfl
  | len + 1, hv => by
    rw [Rcpt.bitsXn, bits_succ]
    have h := evR_bitsXn (cur := cur) (fst := fst) (lst := lst) (pub := pub) off len (fun j h1 h2 => hv j h1 (by omega))
    have hv := hv (off + len) (by omega) (by omega)
    rw [Rcpt.bitsXn, bits] at h
    have e : ∀ (l1 l2 : List Expr), evR cur nx fst lst pub (sum (l1 ++ l2)) =
        evR cur nx fst lst pub (sum l1) + evR cur nx fst lst pub (sum l2) := by
      intro l1 l2; induction l1 with
      | nil => simp; grind
      | cons a l ih => simp [ih]; grind
    rw [e, h]
    simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_n, hv, bitsVal, natCast_eq, ofNat_add_e, ofNat_mul_e]
    grind

/-- Bits `off … off + len − 1` of a pool holding the bits of `x` from `off`. -/
theorem bitsVal_pool {v : Nat → Nat} {off len x : Nat} (hv : ∀ j, j < len → v (off + j) = bitOf x j)
    (hx : x < 2 ^ len) : bitsVal v off len = x := by
  rw [bitsVal_congr off len hv, bitsVal_bitOf, Nat.mod_eq_of_lt hx]

/-! ## Reads -/

/-- Columns read on the current / next row. -/
def colsC : Expr → List Nat
  | .col x false => [x]
  | .add a d | .mul a d => colsC a ++ colsC d
  | .neg a => colsC a
  | _ => []

def colsN : Expr → List Nat
  | .col x true => [x]
  | .add a d | .mul a d => colsN a ++ colsN d
  | .neg a => colsN a
  | _ => []

theorem evR_congr {cur cur' nx nx' : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ e, (∀ x ∈ colsC e, cur x = cur' x) → (∀ x ∈ colsN e, nx x = nx' x) →
      evR cur nx fst lst pub e = evR cur' nx' fst lst pub e
  | .const _, _, _ => rfl
  | .col x false, h, _ => h x (by simp [colsC])
  | .col x true, _, h => h x (by simp [colsN])
  | .pub _, _, _ => rfl
  | .isFirst, _, _ => rfl
  | .isLast, _, _ => rfl
  | .isTransition, _, _ => rfl
  | .add a d, h1, h2 => by
    simp only [evR_add]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx])),
      evR_congr d (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]
  | .mul a d, h1, h2 => by
    simp only [evR_mul]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx])),
      evR_congr d (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]
  | .neg a, h1, h2 => by
    simp only [evR_neg]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]

end RcptP

end ZkFormal.Near.Render
