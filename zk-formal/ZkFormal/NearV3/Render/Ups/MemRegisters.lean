import ZkFormal.NearV3.Render.Ups.Tac

/-! Explicit length-register values and their elementary shift identities. -/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.NearV3.UpsV3
namespace UpsGen

def lrReg (I : UpsInst) (st ix j : Nat) : Int :=
  if st = 4 ∨ st = 8 then Lb I (j + ix) else Lb I j

def srReg (Q : UpsPartI) (st ix j : Nat) : Int :=
  if st = 4 then slb Q ((j + ix) % 4)
  else if st = 8 then slb Q (j + ix) else slb Q j

theorem qc_LR (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u : Nat)
    {j : Nat} (hj : j < 3) :
    QC I Q k p st ix fl wi u (UpsV3.LR j) = lrReg I st ix j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;>
    simp only [UpsV3.LR, lrReg] <;> cellsimp

theorem qc_SR (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u : Nat)
    {j : Nat} (hj : j < 4) :
    QC I Q k p st ix fl wi u (UpsV3.SR j) = srReg Q st ix j := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
    simp only [UpsV3.SR, srReg] <;> cellsimp

theorem lrReg_zero (I : UpsInst) (st j : Nat) : lrReg I st 0 j = Lb I j := by
  simp [lrReg]

theorem srReg_zero (Q : UpsPartI) (st : Nat) {j : Nat} (hj : j < 4) :
    srReg Q st 0 j = slb Q j := by
  simp [srReg, Nat.mod_eq_of_lt hj]

theorem Lb_high (I : UpsInst) {j : Nat} (hj : 3 ≤ j) : Lb I j = 0 := by
  simp only [Lb]
  split <;> omega

theorem lrReg_shift (I : UpsInst) (st ix j : Nat) (hs : st = 4 ∨ st = 8) :
    lrReg I st (ix + 1) j = lrReg I st ix (j + 1) := by
  simp only [lrReg, hs, ite_true]
  congr 1
  omega

theorem lrReg_top_zero (I : UpsInst) (st ix : Nat) (hs : st = 4 ∨ st = 8) :
    lrReg I st (ix + 1) 2 = 0 := by
  simp only [lrReg, hs, ite_true]
  exact Lb_high I (by omega)

theorem srReg_mem_shift (Q : UpsPartI) (ix j : Nat) :
    srReg Q 8 (ix + 1) j = srReg Q 8 ix (j + 1) := by
  simp only [srReg, Nat.reduceEqDiff, ite_false, ite_true]
  congr 1
  omega

theorem srReg_mem_top_zero (Q : UpsPartI) (ix : Nat) : srReg Q 8 (ix + 1) 3 = 0 := by
  simp only [srReg, Nat.reduceEqDiff, ite_false, ite_true, slb]
  rw [if_neg (by omega)]

theorem srReg_vlen_shift (Q : UpsPartI) (ix j : Nat) :
    srReg Q 4 (ix + 1) j = srReg Q 4 ix ((j + 1) % 4) := by
  simp only [srReg, ite_true]
  congr 1
  omega

theorem srReg_vlen_last (Q : UpsPartI) {j : Nat} (hj : j < 4) :
    srReg Q 4 3 ((j + 1) % 4) = slb Q j := by
  simp only [srReg, ite_true]
  congr 1
  omega

theorem srReg_other (Q : UpsPartI) (st ix j : Nat) (h4 : st ≠ 4) (h8 : st ≠ 8) :
    srReg Q st ix j = slb Q j := by simp [srReg, h4, h8]

end UpsGen
end ZkFormal.NearV3.Render
