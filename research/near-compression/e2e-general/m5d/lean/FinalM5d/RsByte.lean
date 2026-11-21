import FinalM5d.RsRow

/-!
# FinalM5d.RsByte — an `RS` row's parity bytes are the spec's `parityPart` bytes

`rs_parity_byte`: on an active `RS` row (constraints, `q` bytes — both from `Holds finalAirS` in
`rs_parity_byte_holds`), the parity byte `i` (`Rs.parByte i`, its 8 bit cells) equals, as a
natural, the byte the spec's `parityPart` computes at that position:
`⊕_j MUL_TABLE[M[d+i][j]][d_j]` over the row's data bytes `d_j = Rs.dataByte j`
(`mulSliceXor`'s per-position step, `UInt8` xor of `mulRow` entries).

From `RsRow.rs_parity_bit` (bit `k` = parity of the selected data bits) and
`RsCoeff.coeff_linear` (bit `k` of `gfMul c x` = the GF(2) sum over `x`'s bits).
-/

namespace FinalM5d.RsByte

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound NearSpecV3 FinalM5d FinalM5d.FinRow
open FinalM5d.Whole FinalM5d.RsRow

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

local notation "PR" => 2013265921

/-- The spec's parity byte at one position: `⊕_j mulRow(M[d+i][j])[d_j]` (`parityPart`'s fold
of `mulSliceXor` restricted to one byte position). -/
def parU8 (i : Nat) (ds : Nat → Nat) : UInt8 :=
  (List.range RSD).foldl (fun acc j => acc ^^^ (mulRow (Rs.matrix.get (RSD + i) j))[ds j]?.getD 0) 0

/-! ## Arithmetic helpers -/

theorem foldl_add {α : Type} (f : α → Nat) : ∀ (l : List α) (a : Nat),
    l.foldl (fun acc m => acc + f m) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add f l]; omega

theorem bits8F : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2, ∀ k : Fin 8,
      (b0.val + 2 * b1.val + 4 * b2.val + 8 * b3.val + 16 * b4.val + 32 * b5.val + 64 * b6.val +
        128 * b7.val) / 2 ^ k.val % 2 =
        [b0.val, b1.val, b2.val, b3.val, b4.val, b5.val, b6.val, b7.val].getD k.val 0 := by
  decide +kernel

theorem bits8 : ∀ b0, b0 < 2 → ∀ b1, b1 < 2 → ∀ b2, b2 < 2 → ∀ b3, b3 < 2 → ∀ b4, b4 < 2 →
    ∀ b5, b5 < 2 → ∀ b6, b6 < 2 → ∀ b7, b7 < 2 → ∀ k, k < 8 →
      (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6 + 128 * b7) / 2 ^ k % 2 =
        [b0, b1, b2, b3, b4, b5, b6, b7].getD k 0 :=
  fun b0 h0 b1 h1 b2 h2 b3 h3 b4 h4 b5 h5 b6 h6 b7 h7 k hk =>
    bits8F ⟨b0, h0⟩ ⟨b1, h1⟩ ⟨b2, h2⟩ ⟨b3, h3⟩ ⟨b4, h4⟩ ⟨b5, h5⟩ ⟨b6, h6⟩ ⟨b7, h7⟩ ⟨k, hk⟩

/-- The value of 8 bit cells. -/
theorem ev_byte8 (f : Nat → Expr) (hb : ∀ m, m < 8 → ev tr t r pub (f m) ≤ 1) :
    ev tr t r pub (sumE ((List.range 8).map fun m => K (2 ^ m) * f m)) =
      ev tr t r pub (f 0) + 2 * ev tr t r pub (f 1) + 4 * ev tr t r pub (f 2) +
      8 * ev tr t r pub (f 3) + 16 * ev tr t r pub (f 4) + 32 * ev tr t r pub (f 5) +
      64 * ev tr t r pub (f 6) + 128 * ev tr t r pub (f 7) := by
  rw [HbWhole.ev_sumE]
  have e8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [e8]
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ev_hmul, ev_K]
  simp only [Nat.reducePow, Nat.reduceMod]
  have sm : ∀ c x, c ≤ 128 → x ≤ 1 → c * x % PR = c * x := fun c x hc hx =>
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul hc hx) (by decide))
  rw [sm 1 _ (by omega) b0, sm 2 _ (by omega) b1, sm 4 _ (by omega) b2, sm 8 _ (by omega) b3,
    sm 16 _ (by omega) b4, sm 32 _ (by omega) b5, sm 64 _ (by omega) b6, sm 128 _ (by omega) b7]
  simp only [Nat.one_mul, Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Bit `k` of an 8-bit-cell byte is its cell `k`. -/
theorem byte8_bit (f : Nat → Expr) (hb : ∀ m, m < 8 → ev tr t r pub (f m) ≤ 1) {k : Nat}
    (hk : k < 8) :
    ev tr t r pub (sumE ((List.range 8).map fun m => K (2 ^ m) * f m)) / 2 ^ k % 2 =
      ev tr t r pub (f k) := by
  rw [ev_byte8 f hb]
  rw [bits8 _ (by have := hb 0 (by omega); omega) _ (by have := hb 1 (by omega); omega)
    _ (by have := hb 2 (by omega); omega) _ (by have := hb 3 (by omega); omega)
    _ (by have := hb 4 (by omega); omega) _ (by have := hb 5 (by omega); omega)
    _ (by have := hb 6 (by omega); omega) _ (by have := hb 7 (by omega); omega) k hk]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem byte8_lt (f : Nat → Expr) (hb : ∀ m, m < 8 → ev tr t r pub (f m) ≤ 1) :
    ev tr t r pub (sumE ((List.range 8).map fun m => K (2 ^ m) * f m)) < 256 := by
  rw [ev_byte8 f hb]
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  have b3 := hb 3 (by omega); have b4 := hb 4 (by omega); have b5 := hb 5 (by omega)
  have b6 := hb 6 (by omega); have b7 := hb 7 (by omega)
  omega

/-! ## The class matrix -/

/-- Every parity coefficient is one `coeff_linear` covers. -/
theorem mat_mem : ∀ i, i < NPAR → ∀ j, j < RSD → Rs.matrix.get (RSD + i) j ∈ RsCoeff.coeffs := by
  decide +kernel

theorem linAt_of {i j : Nat} (hi : i < NPAR) (hj : j < RSD) {x k : Nat} (hx : x < 256) (hk : k < 8) :
    RsCoeff.linAt (Rs.matrix.get (RSD + i) j) x k = true := by
  have := List.all_eq_true.1 RsCoeff.coeff_linear _ (mat_mem i hi j hj)
  have := List.all_eq_true.1 this x (List.mem_range.2 hx)
  exact List.all_eq_true.1 this k (List.mem_range.2 hk)

theorem mulBit_le (c k m : Nat) : Rs.mulBit c k m ≤ 1 := by
  unfold Rs.mulBit; omega

/-- Bit `k` of `gfMul c x` (`x < 256`, `c` a class coefficient) as a sum mod 2. -/
theorem gfMul_bit {i j : Nat} (hi : i < NPAR) (hj : j < RSD) {x k : Nat} (hx : x < 256) (hk : k < 8) :
    gfMul (Rs.matrix.get (RSD + i) j) x / 2 ^ k % 2 =
      ((List.range 8).map fun m => (x / 2 ^ m % 2) * Rs.mulBit (Rs.matrix.get (RSD + i) j) k m).sum % 2 := by
  have := linAt_of hi hj hx hk
  unfold RsCoeff.linAt at this
  rw [foldl_add] at this
  simp only [Nat.zero_add, beq_iff_eq] at this
  exact this.symm

/-! ## The selected sum, per data part -/

theorem filterMap_sum (c k j : Nat) : ∀ (ms : List Nat),
    ((ms.filterMap fun m => if Rs.mulBit c k m == 1 then some (Rs.T.c "x" (8 * j + m)) else none).map
      (ev tr t r pub)).sum =
    (ms.map fun m => Rs.mulBit c k m * ev tr t r pub (Rs.T.c "x" (8 * j + m))).sum
  | [] => by simp
  | m :: ms => by
    have ih := filterMap_sum c k j ms
    have hm := mulBit_le c k m
    by_cases h : Rs.mulBit c k m = 1
    · simp only [List.filterMap_cons, h, beq_self_eq_true, ite_true, List.map_cons, List.sum_cons, ih,
        Nat.one_mul]
    · have h0 : Rs.mulBit c k m = 0 := by omega
      simp only [List.filterMap_cons, h0, show ((0 : Nat) == 1) = false from rfl, Bool.false_eq_true,
        ite_false, List.map_cons, List.sum_cons, ih, Nat.zero_mul, Nat.zero_add]

theorem sum_flatMap {α β : Type} (f : α → List β) (g : β → Nat) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun j => ((f j).map g).sum).sum
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_flatMap f g l]

theorem sel_sum (i k : Nat) : ((sel i k).map (ev tr t r pub)).sum =
    ((List.range RSD).map fun j => ((List.range 8).map fun m =>
      Rs.mulBit (Rs.matrix.get (RSD + i) j) k m * ev tr t r pub (Rs.T.c "x" (8 * j + m))).sum).sum := by
  unfold sel
  rw [sum_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  exact filterMap_sum _ k j _

/-! ## XOR folds and sums mod 2 -/

theorem testBit_foldl_xor {α : Type} (g : α → UInt8) (k : Nat) : ∀ (l : List α) (a : UInt8),
    (l.foldl (fun acc j => acc ^^^ g j) a).toNat.testBit k =
      decide (((a.toNat / 2 ^ k % 2) + (l.map fun j => (g j).toNat / 2 ^ k % 2).sum) % 2 = 1)
  | [], a => by
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero, Nat.testBit_eq_decide_div_mod_eq,
      Nat.mod_mod]
  | x :: l, a => by
    rw [List.foldl_cons, testBit_foldl_xor g k l]
    simp only [UInt8.toNat_xor, List.map_cons, List.sum_cons]
    generalize (l.map fun j => (g j).toNat / 2 ^ k % 2).sum = S
    have h1 : (a.toNat ^^^ (g x).toNat) / 2 ^ k % 2 =
        (a.toNat / 2 ^ k % 2 + (g x).toNat / 2 ^ k % 2) % 2 := by
      have := Nat.testBit_xor a.toNat (g x).toNat k
      simp only [Nat.testBit_eq_decide_div_mod_eq] at this
      have ha := Nat.mod_lt (a.toNat / 2 ^ k) (show 0 < 2 by decide)
      have hb := Nat.mod_lt ((g x).toNat / 2 ^ k) (show 0 < 2 by decide)
      have hc := Nat.mod_lt ((a.toNat ^^^ (g x).toNat) / 2 ^ k) (show 0 < 2 by decide)
      revert this ha hb hc
      generalize (a.toNat ^^^ (g x).toNat) / 2 ^ k % 2 = C
      generalize a.toNat / 2 ^ k % 2 = A
      generalize (g x).toNat / 2 ^ k % 2 = B
      intro this ha hb hc
      rcases (show A = 0 ∨ A = 1 by omega) with rfl | rfl <;>
      rcases (show B = 0 ∨ B = 1 by omega) with rfl | rfl <;>
      rcases (show C = 0 ∨ C = 1 by omega) with rfl | rfl <;> simp_all
    have key : ((a.toNat ^^^ (g x).toNat) / 2 ^ k % 2 + S) % 2 =
        (a.toNat / 2 ^ k % 2 + ((g x).toNat / 2 ^ k % 2 + S)) % 2 := by
      rw [h1]; omega
    rw [key]

theorem mulRow_get {c x : Nat} (hx : x < 256) :
    ((mulRow c)[x]?.getD 0).toNat = gfMul c x % 256 := by
  unfold mulRow
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range hx]
  simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat']

theorem mod256_bit (n k : Nat) (hk : k < 8) : n % 256 / 2 ^ k % 2 = n / 2 ^ k % 2 := by
  have h := Nat.testBit_mod_two_pow n 8 k
  simp only [Nat.testBit_eq_decide_div_mod_eq, hk, decide_true, Bool.true_and, Nat.reducePow] at h
  have ha := Nat.mod_lt (n % 256 / 2 ^ k) (show 0 < 2 by decide)
  have hb := Nat.mod_lt (n / 2 ^ k) (show 0 < 2 by decide)
  revert h ha hb
  generalize n % 256 / 2 ^ k % 2 = A
  generalize n / 2 ^ k % 2 = B
  intro h ha hb
  rcases (show A = 0 ∨ A = 1 by omega) with rfl | rfl <;>
  rcases (show B = 0 ∨ B = 1 by omega) with rfl | rfl <;> simp_all

theorem sum_mod2 : ∀ l : List Nat, ((l.map (· % 2)).sum) % 2 = l.sum % 2
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_mod2 l
    omega

/-! ## The parity byte -/

section
variable (hc : ∀ e ∈ Rs.constraints, e.eval tr t r pub = 0)
include hc

theorem data_bit {j m : Nat} (hj : j < RSD) (hm : m < 8) :
    ev tr t r pub (Rs.dataByte j) / 2 ^ m % 2 = ev tr t r pub (Rs.T.c "x" (8 * j + m)) :=
  byte8_bit (fun m => Rs.T.c "x" (8 * j + m))
    (fun m hm => x_bool hc (by simp only [RSD] at hj ⊢; omega)) hm

theorem data_lt {j : Nat} (hj : j < RSD) : ev tr t r pub (Rs.dataByte j) < 256 :=
  byte8_lt (fun m => Rs.T.c "x" (8 * j + m)) (fun m hm => x_bool hc (by simp only [RSD] at hj ⊢; omega))

/-- **Parity byte `i` of an `RS` row is the spec's parity byte** of the row's data bytes. -/
theorem rs_parity_byte (hact : ev tr t r pub Rs.act = 1)
    (hq : ∀ c, c < 8 * NPAR → ev tr t r pub (Rs.T.c "q" c) < 256) {i : Nat} (hi : i < NPAR) :
    ev tr t r pub (Rs.parByte i) = (parU8 i fun j => ev tr t r pub (Rs.dataByte j)).toNat := by
  have hrb : ∀ k, k < 8 → ev tr t r pub (Rs.T.c "r" (8 * i + k)) ≤ 1 := fun k hk =>
    r_bool hc (by simp only [NPAR, RST, RSD] at hi ⊢; omega)
  have hL : ev tr t r pub (Rs.parByte i) < 256 := byte8_lt (fun k => Rs.T.c "r" (8 * i + k)) hrb
  have hR := (parU8 i fun j => ev tr t r pub (Rs.dataByte j)).toNat_lt
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 8
  · rw [Nat.testBit_eq_decide_div_mod_eq, parU8, testBit_foldl_xor]
    congr 1
    -- left: the parity bit
    have e1 : ev tr t r pub (Rs.parByte i) / 2 ^ k % 2 = ev tr t r pub (Rs.T.c "r" (8 * i + k)) :=
      byte8_bit (fun k => Rs.T.c "r" (8 * i + k)) hrb hk
    rw [e1, rs_parity_bit hc hact hq hi hk, sel_sum]
    -- right: the xor fold
    have e2 : ((List.range RSD).map fun j =>
        ((mulRow (Rs.matrix.get (RSD + i) j))[ev tr t r pub (Rs.dataByte j)]?.getD 0).toNat / 2 ^ k % 2) =
        ((List.range RSD).map fun j => ((List.range 8).map fun m =>
          Rs.mulBit (Rs.matrix.get (RSD + i) j) k m * ev tr t r pub (Rs.T.c "x" (8 * j + m))).sum % 2) := by
      apply List.map_congr_left
      intro j hj
      have hj' := List.mem_range.1 hj
      rw [mulRow_get (data_lt hc hj'), mod256_bit _ _ hk, gfMul_bit hi hj' (data_lt hc hj') hk]
      congr 2
      apply List.map_congr_left
      intro m hm
      rw [data_bit hc hj' (List.mem_range.1 hm), Nat.mul_comm]
    rw [e2]
    simp only [UInt8.toNat_zero, Nat.zero_div, Nat.zero_mod, Nat.zero_add]
    have := sum_mod2 ((List.range RSD).map fun j => ((List.range 8).map fun m =>
      Rs.mulBit (Rs.matrix.get (RSD + i) j) k m * ev tr t r pub (Rs.T.c "x" (8 * j + m))).sum)
    simp only [List.map_map, Function.comp_def] at this
    rw [this]
  · have h8 : 256 ≤ 2 ^ k := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 8 ≤ k by omega)
      simpa using this
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

end

/-- **`rs_parity_byte` from `Holds finalAirS`.** -/
theorem rs_parity_byte_holds (h : Holds finalAirS pub tr) {r : Nat} (hr : r < tr.height 7)
    (hact : ev tr 7 r pub Rs.act = 1) {i : Nat} (hi : i < NPAR) :
    ev tr 7 r pub (Rs.parByte i) = (parU8 i fun j => ev tr 7 r pub (Rs.dataByte j)).toNat :=
  rs_parity_byte (rs_constr h hr) hact (fun _ hc => rs_q_lt h hr hact hc) hi

end FinalM5d.RsByte
