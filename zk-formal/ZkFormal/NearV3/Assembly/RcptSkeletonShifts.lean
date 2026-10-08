import ZkFormal.NearV3.Assembly.RcptSkeletonLoads

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def shiftConstraints : List Expr := (List.range 31).map fun j=>
  mul3 (c act) (Dsl.not (c fe)) (sub (n (reg j)) (c (reg (j+1))))

theorem shiftConstraints_in_regs : ∀e∈shiftConstraints,e∈cRegs := by
  intro e he
  simp only [shiftConstraints] at he
  simp only [cRegs,List.mem_append]
  grind only

theorem receipt_register_shift (constants : ReceiptPlan→Nat→Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (pub : List Fp) (j : Nat) (hj : j<31) :
    receiptCell constants (registerAux pub fallback) plan (advance row) (reg j)=
      receiptCell constants (registerAux pub fallback) plan row (reg (j+1)) := by
  rw [receipt_register_cell constants fallback plan (advance row) pub j (by omega),
    receipt_register_cell constants fallback plan row pub (j+1) (by omega)]
  exact registerCell_shift _ _ _ hj

/-- All 31 original register-shift polynomials hold between actual advancing
receipt coordinates of the shared constructor. -/
theorem receipt_shift_constraints (constants : ReceiptPlan→Nat→Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (pub : List Fp) :
    ∀e∈shiftConstraints,e.eval
      (receiptPair constants (registerAux pub fallback) plan row (advance row)) 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  have hh := receipt_register_shift constants fallback plan row pub j hj'
  simp only [eval_mul3,eval_c,eval_not,eval_sub,eval_n]
  change _*_* (receiptCell constants (registerAux pub fallback) plan (advance row) (reg j)-
    receiptCell constants (registerAux pub fallback) plan row (reg (j+1)))=0
  rw [hh]
  grind only

theorem receipt_shift_at_end (constants : ReceiptPlan→Nat→Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row next : Coord)
    (pub : List Fp) (hend : row.index+1=row.length) :
    ∀e∈shiftConstraints,e.eval
      (receiptPair constants (registerAux pub fallback) plan row next) 0 0 pub=0 := by
  intro e he
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
  have hfe : (receiptPair constants (registerAux pub fallback) plan row next).cell 0 0 fe=1 := by
    change receiptCell constants (registerAux pub fallback) plan row fe=1
    rw [receipt_control_cell constants _ plan row (by decide)]
    change (if row.index+1=row.length then (1:Fp) else 0)=1
    rw [if_pos hend]
  simp only [eval_mul3,eval_c,eval_not,hfe]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
