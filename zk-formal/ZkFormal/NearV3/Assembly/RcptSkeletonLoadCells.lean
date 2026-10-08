import ZkFormal.NearV3.Assembly.RcptSkeletonLoadExpr

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def registerAux (pub : List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (plan : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if reg 0≤col ∧ col<reg 32 then
    registerCell (registerLoad plan.input pub row.state) row.index col
  else fallback plan row col

theorem receipt_register_cell (constants : ReceiptPlan→Nat→Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (plan : ReceiptPlan) (row : Coord)
    (pub : List Fp) (j : Nat) (hj : j<32) :
    receiptCell constants (registerAux pub fallback) plan row (reg j)=
      registerCell (registerLoad plan.input pub row.state) row.index (reg j) := by
  have he : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 ∨ j=12 ∨ j=13 ∨ j=14 ∨ j=15 ∨ j=16 ∨ j=17 ∨ j=18 ∨ j=19 ∨ j=20 ∨ j=21 ∨ j=22 ∨ j=23 ∨ j=24 ∨ j=25 ∨ j=26 ∨ j=27 ∨ j=28 ∨ j=29 ∨ j=30 ∨ j=31 := by omega
  rcases he with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> rfl

theorem loads_states : ∀p∈loads,p.1∈states := by decide

def loadConstraints : List Expr := loads.flatMap fun (s,es)=>
  (es.zip (List.range es.length)).map fun (e,j)=>mul3 (c s) (c fs) (sub (c (reg j)) e)

theorem loadConstraints_in_regs : ∀e∈loadConstraints,e∈cRegs := by
  intro e he
  simp only [loadConstraints] at he
  simp only [cRegs,List.mem_append]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
