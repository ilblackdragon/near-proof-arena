import ZkFormal.NearV3.Assembly.RcptStateSuccessorPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptFirstConstraints : List Expr :=
  [.mul (c rf) (Dsl.not (c sPL)),.mul (c rf) (Dsl.not (c fs)),
   mul3 (c sPL) (c fs) (Dsl.not (c rf)),.mul (c rf) (c idx)]

theorem receiptFirstConstraints_footprint : receiptFirstConstraints.all currentExpr=true ∧
    receiptFirstConstraints.all noEmissionExpr=true := by decide

theorem receiptFirstConstraints_in_states : ∀e∈receiptFirstConstraints,e∈cStates := by
  intro e he
  simp only [receiptFirstConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem receipt_firstFlags (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (pub : List Fp) :
    ∀e∈receiptFirstConstraints,e.eval (receiptPair constants aux p row row) 0 0 pub=0 := by
  have hrf : (receiptPair constants aux p row row).cell 0 0 rf=
      if row.state=sPL ∧ row.index=0 then 1 else 0 := by
    change bitCell (row.state==sPL && row.index==0)=_
    simp only [bitCell,Bool.and_eq_true,beq_iff_eq]
  have hstate : (receiptPair constants aux p row row).cell 0 0 sPL=if row.state=sPL then 1 else 0 := by
    have hh := (receipt_control_cell constants aux p row (c:=sPL) (by decide)).trans (control_state row (by decide : sPL∈states))
    simpa only [receiptPair,ite_true,eq_comm] using hh
  have hfs : (receiptPair constants aux p row row).cell 0 0 fs=if row.index=0 then 1 else 0 := receipt_control_cell constants aux p row (c:=fs) (by decide)
  have hidx : (receiptPair constants aux p row row).cell 0 0 idx=Fp.ofNat row.index := receipt_control_cell constants aux p row (c:=idx) (by decide)
  intro e he
  simp only [receiptFirstConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl <;>
    simp only [eval_mul,eval_mul3,eval_c,eval_not,hrf,hstate,hfs,hidx]
  all_goals by_cases hs : row.state=sPL <;> by_cases hi : row.index=0 <;> simp only [hs,hi,↓reduceIte,not_false_eq_true,and_true,and_false,true_and,false_and]
  all_goals first | (change (1:Fp)*0=0;grind only) | grind only

theorem header_firstFlags (aux : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat) (pub : List Fp) :
    ∀e∈receiptFirstConstraints,e.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
  have hr : headerCell aux p ⟨sCL,i,12⟩ rf=0 := rfl
  have hs : headerCell aux p ⟨sCL,i,12⟩ sPL=0 := rfl
  intro e he
  simp only [receiptFirstConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl <;> simp only [eval_mul,eval_mul3,eval_c,eval_not] <;>
    change _=0
  all_goals simp only [hr,hs]
  all_goals grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
