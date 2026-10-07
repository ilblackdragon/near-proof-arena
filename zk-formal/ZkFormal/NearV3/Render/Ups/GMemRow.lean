import ZkFormal.NearV3.Render.Ups.WideBits
import Init.Data.Int.OfNat
import ZkFormal.NearV3.Render.Ups.Tac
import ZkFormal.NearV3.Render.Ups.MemArith

/-! Reconstruction of the memory row's encoded integer limbs and carries.
These row proofs require the actual carry ranges and the serialized memory byte.
They do not yet establish those inputs from a trie update, the register shifts,
or the full `cMem` group on the generated trace. -/
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3
namespace UpsGen

section
variable {C D P : Nat → Int} {fst lst trn : Int}
variable {I : UpsInst} {Q : UpsPartI} {k p ix wi u : Nat}
variable (hC : ∀ x, x < 200 → C x = QC I Q k p 8 ix 8 wi u x)

private theorem memWin : winFrV I Q 8 wi = 0 := rfl

include hC

/-- The memory row's eight bit cells reconstruct T's byte. -/
theorem mem_tE : ev C D fst lst trn P UpsV3.tE = tV I Q ix := by
  have hb := byte_bits (tV I Q ix)
    (by unfold tV; omega) (by unfold tV; omega)
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub, Int.reducePow, Int.ediv_one, Int.zero_add, Int.one_mul]
  omega

/-- Three carry bits reconstruct cb when its representable range is proved. -/
theorem mem_cbE (h0 : 0 ≤ cbV I Q ix) (h1 : cbV I Q ix < 131072) :
    ev C D fst lst trn P UpsV3.cbE = cbV I Q ix := by
  have hb := carry_bits17 (cbV I Q ix) h0 h1
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Int.reducePow,Int.ediv_one,Int.one_mul,
    Int.zero_add,Int.add_zero] at hb
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub, Int.reducePow, Int.ediv_one, Int.zero_add, Int.one_mul]
  omega

/-- Three carry bits reconstruct the outside carry when its range is proved. -/
theorem mem_ccE (h0 : 0 ≤ co2V I Q ix) (h1 : co2V I Q ix < 65536) :
    ev C D fst lst trn P UpsV3.ccE = co2V I Q ix := by
  have hb := carry_bits16 (co2V I Q ix) h0 h1
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Int.reducePow,Int.ediv_one,Int.one_mul,
    Int.zero_add,Int.add_zero] at hb
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub, Int.reducePow, Int.ediv_one, Int.zero_add, Int.one_mul]
  omega

/-- Removing the non-final-row bias recovers the signed inside carry. -/
theorem mem_coE (hi : ix < 8) (h0 : 0 ≤ cbV I Q ix) (h1 : cbV I Q ix < 131072) :
    ev C D fst lst trn P UpsV3.coE = coV I Q ix := by
  simp only [coE, ev]
  rw [mem_cbE hC h0 h1]
  ups_ev [hC]
  cellsimp
  simp only [cbV, ind]
  split <;> split <;> omega

/-- The encoded inside-chain equation is the proved signed carry recurrence. -/
theorem mem_inside (hi : ix < 8) (h0 : 0 ≤ cbV I Q ix) (h1 : cbV I Q ix < 131072) :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 6 (Dsl.k 0)) : Int) : Fp) = 0 := by
  change ((ev C D fst lst trn P (.mul (c sMEM)
    (sub (.add (.mul sigE (c X1)) (c ci)) (.add tE (smul 256 coE)))) : Int) : Fp) = 0
  apply cast0
  simp only [ev, Dsl.sub, Dsl.smul]
  rw [mem_tE hC, mem_coE hC hi h0 h1]
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub,
    ind_True, Int.one_mul, Int.sub_zero]
  change (sigV Q * X1V I Q ix + (if ix = 0 then 0 else coV I Q (ix - 1))) -
    (tV I Q ix + 256 * coV I Q ix) = 0
  exact Int.sub_eq_zero.mpr (inside_carry I Q hi)

/-- The inside arithmetic input is exactly A + B − C from the source and child limbs. -/
theorem mem_input :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 0 (Dsl.k 0)) : Int) : Fp) = 0 := by
  apply cast0
  change ev C D fst lst trn P (.mul (c sMEM) (sub (c X1)
    (sub (sum [.mul (c useA) (c rb), .mul (c UpsV3.bN) (c mBv), .mul (c bL) (c (LR 0))])
      (sum [.mul (c cO) (c mCv), .mul (c cS) (c (SR 0)), .mul (c fs) (c Cc)])))) = 0
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub,
    ind_True, Int.one_mul, Int.sub_zero, X1V, Ai, Bi, Ci, rbV, sposV, memRb]
  omega

/-- The outside arithmetic input is the generator's exact E limb. -/
theorem mem_extra :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 1 (Dsl.k 0)) : Int) : Fp) = 0 := by
  apply cast0
  change ev C D fst lst trn P (.mul (c sMEM) (sub (c Ein)
    (sum [.mul (c fs) (c Kc), .mul (c eL) (c (LR 0)), .mul (c eS) (c (SR 0))]))) = 0
  ups_ev [hC]
  cellsimp
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub,
    ind_True, Int.one_mul, Int.sub_zero, EinV]
  omega

/-- The stored memory byte closes the outside carry equation. -/
theorem mem_outside (hi : ix < 8) (hn : Q.neg ≤ 1)
    (h0 : 0 ≤ co2V I Q ix) (h1 : co2V I Q ix < 65536)
    (hb : (Q.q.getD p 0 : Int) = RV I Q / 256 ^ ix % 256) :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 7 (Dsl.k 0)) : Int) : Fp) = 0 := by
  change ((ev C D fst lst trn P (.mul (c sMEM)
    (sub (sum [c Ein, .mul (Dsl.not (c UpsV3.neg)) tE, c ci2])
      (.add (c UpsV3.b) (smul 256 ccE)))) : Int) : Fp) = 0
  apply cast0
  simp only [ev, Dsl.sub, Dsl.smul, Dsl.sum]
  rw [mem_tE hC, mem_ccE hC h0 h1]
  ups_ev [hC]
  cellsimp
  rw [hb]
  simp only [memWin, show (0 : Int) ≠ 1 by decide, ite_false, memReg,
    or_false, false_or, ite_true, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub,
    ind_True, Int.one_mul, Int.sub_zero]
  change (EinV I Q ix + ((1 - (Q.neg : Int)) * tV I Q ix +
    ((if ix = 0 then 0 else co2V I Q (ix - 1)) + 0))) -
    (RV I Q / 256 ^ ix % 256 + 256 * co2V I Q ix) = 0
  have h := outside_carry I Q hn hi
  omega

/-- The parent receives the exact final limb rather than a truncated byte. -/
theorem mem_parent (hi : ix < 8) (hn : Q.neg ≤ 1)
    (hb0 : 0 ≤ cbV I Q ix) (hb1 : cbV I Q ix < 131072)
    (hc0 : 0 ≤ co2V I Q ix) (hc1 : co2V I Q ix < 65536)
    (hb : (Q.q.getD p 0 : Int) = RV I Q / 256 ^ ix % 256) :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 8 (Dsl.k 0)) : Int) : Fp) = 0 := by
  change ((ev C D fst lst trn P (.mul (c sMEM)
    (sub (c rx) (.add (c UpsV3.b) (smul 256 (.mul (c fe)
      (.add (.mul (Dsl.not (c UpsV3.neg)) cbE) ccE)))))) : Int) : Fp) = 0
  apply cast0
  simp only [ev, Dsl.sub, Dsl.smul]
  rw [mem_cbE hC hb0 hb1, mem_ccE hC hc0 hc1]
  ups_ev [hC]
  cellsimp
  rw [hb]
  simp only [ind_True, Int.one_mul]
  by_cases h7 : ix = 7
  · subst ix
    have h := outside_last_high I Q hn
    simp only [ind, cbV, Nat.reduceAdd, Nat.reduceLT, ite_true, ite_false,
      Int.add_zero, Int.one_mul, Int.sub_eq_add_neg, Nat.ToInt.natCast_ofNat] at h ⊢
    change limb (RV I Q) 7 - (RV I Q / 256 ^ 7 % 256 +
      256 * ((1 - (Q.neg : Int)) * coV I Q 7 + co2V I Q 7)) = 0
    exact Int.sub_eq_zero.mpr (outside_last_high I Q hn)
  · have hlt : ix < 7 := by omega
    have hn8 : ix + 1 ≠ 8 := by omega
    simp [limb, hlt, ind, hn8, h7]; omega

/-- Both carry chains start at zero on the first memory byte. -/
theorem mem_initial : ∀ e ∈ (UpsV3.cMem.drop 2).take 2,
    ((ev C D fst lst trn P e : Int) : Fp) = 0 := by
  intro e he
  change e ∈ [mul3 (c sMEM) (c fs) (c ci), mul3 (c sMEM) (c fs) (c ci2)] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> apply cast0 <;> ups_ev [hC] <;> cellsimp <;>
    simp [memWin, memReg, ind] <;> split <;> simp_all

/-- Exact gate for sending the part's memory value to its parent. -/
theorem mem_send_gate :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 9 (Dsl.k 0)) : Int) : Fp) = 0 := by
  apply cast0
  change ev C D fst lst trn P (sub (c gMs)
    (mul3 (c sMEM) (Dsl.not (c rootP)) (Dsl.not (c kNLF)))) = 0
  ups_ev [hC]
  cellsimp
  simp only [ind]
  repeat' split <;> simp_all

/-- Exact gate for receiving the selected child's memory value. -/
theorem mem_recv_gate :
    ((ev C D fst lst trn P (UpsV3.cMem.getD 10 (Dsl.k 0)) : Int) : Fp) = 0 := by
  apply cast0
  change ev C D fst lst trn P (sub (c gMr) (.mul (c sMEM) (c UpsV3.bN))) = 0
  ups_ev [hC]
  cellsimp
  simp only [bNV, kin, spRecv, cin, List.map, List.sum_cons, List.sum_nil, ind]
  (repeat' split) <;> simp_all <;> omega

end
end UpsGen
end ZkFormal.NearV3.Render
