import ZkFormal.NearV3.Assembly.RcptRoutingCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

theorem routingColumn_split (col : Nat) (hc : routingColumn col=true) :
    col∈[sV,sRID,fs,idx,Lv,b] ∨ routingScratch col=true := by
  simp only [routingColumn,routingScratch,Bool.or_eq_true,decide_eq_true_eq,
    List.mem_cons,List.not_mem_nil,or_false] at *
  grind only

theorem routingAdjusted_scratch (f : RouteFrame) (len : Nat) (rb : Fp) (col : Nat)
    (hc : routingScratch col=true) : routingAdjustedCell f len rb col=frameCell f col := by
  have hh := routingScratch_bounds col hc
  apply routingAdjusted_other
  simp only [idx,Lv,b]
  omega

set_option maxRecDepth 4096 in
theorem routing_receiver_current (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (i len : Nat) (hi : i<p.input.receipt.receiverId.length)
    (col : Nat) (hc : routingColumn col=true) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p ⟨sV,i,len⟩ col=
      routingAdjustedCell (frameOf p.input.receipt.receiverId (interval p) i)
        p.input.receipt.receiverId.length 0 col := by
  rcases routingColumn_split col hc with hh|hh
  · have hne : i≠p.input.receipt.receiverId.length := by omega
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [receiptCell,controlCell,shapeCell,tokenReceiptAux,streamAux,
      rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,idx,act,fs,fe,sV,sRID,b,reg,tok,
      Nat.reduceAdd,Nat.reduceLeDiff,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceBEq,decide_true,decide_false,
      Bool.false_or,Bool.true_or,Bool.or_true,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
    all_goals simp only [routingAdjustedCell,frameOf,hne,decide_false,idx,Lv,b,Nat.reduceBEq,
      Bool.false_and,Bool.true_and,Bool.not_false,Bool.false_eq_true,ite_false,ite_true]
    all_goals try rfl
    all_goals simp only [frameCell,frameOf,hne,decide_false,iL,iH,sV,sRID,fs,idx,Lv,iB,b,vB,
      Nat.reduceEqDiff,decide_true,decide_false,Bool.false_or,Bool.or_false,Bool.true_or,Bool.or_true,
      Bool.false_eq_true,ite_true,ite_false]
    all_goals try rfl
    all_goals try simp only [nativeFieldByte,regStates,sV,sP,List.mem_cons,List.not_mem_nil,or_false,
      sPL,sVL,sSL,sGP,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,
      Nat.reduceEqDiff,ite_false]
    all_goals try rfl
    all_goals split <;> simp_all only [decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false]
  · rw [routingAdjusted_scratch _ _ _ col hh]
    exact routingAux_transport interval constants pub digests tokens fallback p ⟨sV,i,len⟩ col
      (by simp only [routingActive,beq_self_eq_true,Bool.true_or]) hh

end ZkFormal.NearV3.Assembly.RcptSkeleton
