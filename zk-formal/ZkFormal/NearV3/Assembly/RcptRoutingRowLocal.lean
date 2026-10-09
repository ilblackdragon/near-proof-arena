import ZkFormal.NearV3.Assembly.RcptRoutingNext

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routing_rid_local (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (len : Nat) (next : Coord)
    (hv : inInterval p.input.receipt.receiverId (interval p)=true)
    (hu : ∀v∈(interval p).2.getD [],0<v.toNat) :
    ∀e∈cRoute,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p ⟨sRID,0,len⟩ next) 0 0 pub=0 := by
  intro e he
  let f := frameOf p.input.receipt.receiverId (interval p) p.input.receipt.receiverId.length
  let rb := Fp.ofNat ((p.input.receipt.receiptId.getD 0 0).toNat)
  rw [routing_no_next _ (routingAdjustedTrace f p.input.receipt.receiverId.length rb) 0 0 0 0 pub
    (routing_rid_current interval constants pub digests tokens fallback p len) rfl e he]
  exact routingAdjusted_local f (frameOf_ordered _ _ _ (Nat.le_refl _) hv hu) _ rb pub e he

theorem routing_inactive_cells (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (ha : routingActive row=false) :
    let c := receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p row
    c sV=0 ∧ c sRID*c fs=0 ∧ c gBd=0 := by
  have hv : row.state≠sV := by
    intro h
    simp only [routingActive,h,beq_self_eq_true,Bool.true_or] at ha
    contradiction
  have hr : row.state≠sRID ∨ row.index≠0 := by
    by_cases hs : row.state=sRID
    · apply Or.inr
      intro hi
      simp only [routingActive,hs,hi,beq_self_eq_true,Bool.true_and,Bool.or_true] at ha
      contradiction
    · exact Or.inl hs
  refine ⟨?_,?_,?_⟩
  · change (if sV=row.state then (1:Fp) else 0)=0
    exact if_neg (Ne.symm hv)
  · change (if sRID=row.state then (1:Fp) else 0)*(if row.index=0 then 1 else 0)=0
    rcases hr with hr|hr
    · rw [if_neg (Ne.symm hr)];grind only
    · rw [if_neg hr];grind only
  · simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
      gBd,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
      decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_false,ite_true]
    change boolInput gBd (routingAux interval fallback p row gBd)=0
    rw [routingAux_gate_zero interval fallback p row ha]
    exact boolInput_preserves _ _ (Or.inl rfl)

theorem routing_inactive_local (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row next : Coord) (ha : routingActive row=false) :
    ∀e∈cRoute,e.eval (receiptPair (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p row next) 0 0 pub=0 := by
  have hh := routing_inactive_cells interval constants pub digests tokens fallback p row ha
  exact routing_inactive _ _ _ _ hh.1 hh.2.1 hh.2.2

end ZkFormal.NearV3.Assembly.RcptSkeleton
