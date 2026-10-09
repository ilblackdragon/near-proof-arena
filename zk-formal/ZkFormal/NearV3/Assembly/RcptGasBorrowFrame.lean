import ZkFormal.NearV3.Assembly.RcptGasBorrow

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

/-- The native price subtraction owns only GP-row borrow and difference cells. -/
def gasBorrowAux (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sGP then
    if col=c1 then Fp.ofNat (gasBorrow ctx p.input.receipt row.index) else
    if xb 0≤col ∧ col<xb 8 then frameBit (gasDifference ctx p.input.receipt row.index) (col-xb 0) else
    if col=xb 8 then Fp.ofNat (gasBorrow ctx p.input.receipt (row.index+1)) else fallback p row col
  else fallback p row col

set_option maxRecDepth 4096 in
theorem gasDifference_bit_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len j : Nat) (hj : j<8) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p ⟨sGP,i,len⟩ (xb j)=
      frameBit (gasDifference ctx p.input.receipt i) j := by
  have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,gasBorrowAux,
    c1,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
    kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sGP,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
    List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
    decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
  all_goals exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem gasBorrow_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p ⟨sGP,i,len⟩ c1=
      Fp.ofNat (gasBorrow ctx p.input.receipt i) := rfl

set_option maxRecDepth 4096 in
theorem gasBorrow_next_bit_cell (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p ⟨sGP,i,len⟩ (xb 8)=
      Fp.ofNat (gasBorrow ctx p.input.receipt (i+1)) := by
  change boolInput (xb 8) (Fp.ofNat (gasBorrow ctx p.input.receipt (i+1)))=_
  apply boolInput_preserves
  have hh := gasBorrow_le ctx p.input.receipt (i+1)
  have he : gasBorrow ctx p.input.receipt (i+1)=0 ∨ gasBorrow ctx p.input.receipt (i+1)=1 := by omega
  rcases he with he|he
  · left;rw [he];rfl
  · right;rw [he];rfl

theorem gasDifference_eval (ctx : ApplyCtx)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (next : Coord) :
    DE.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (gasBorrowAux ctx fallback))) p ⟨sGP,i,len⟩ next) 0 0 pub=
      Fp.ofNat (gasDifference ctx p.input.receipt i) := by
  rw [show DE=bitsX 0 8 from rfl,eval_frame_bits _ 0 0 pub 0 (gasDifference ctx p.input.receipt i) 8
    (fun j hj=>by simpa only [Nat.zero_add,receiptPair,ite_true] using gasDifference_bit_cell ctx constants pub digests tokens fallback p i len j hj)]
  rw [Nat.mod_eq_of_lt (gasDifference_lt ctx p.input.receipt i)]

end ZkFormal.NearV3.Assembly.RcptSkeleton
