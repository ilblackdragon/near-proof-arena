import ZkFormal.NearV3.Assembly.RcptRoutingReceiver

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

set_option maxRecDepth 4096 in
theorem routing_rid_current (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (len : Nat)
    (col : Nat) (hc : routingColumn col=true) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (routingAux interval fallback))) p ⟨sRID,0,len⟩ col=
      routingAdjustedCell (frameOf p.input.receipt.receiverId (interval p) p.input.receipt.receiverId.length)
        p.input.receipt.receiverId.length (Fp.ofNat ((p.input.receipt.receiptId.getD 0 0).toNat)) col := by
  rcases routingColumn_split col hc with hh|hh
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [receiptCell,controlCell,shapeCell,tokenReceiptAux,streamAux,
      rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,idx,act,fs,fe,sV,sRID,b,reg,tok,
      Nat.reduceAdd,Nat.reduceLeDiff,Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceBEq,decide_true,decide_false,
      Bool.false_or,Bool.true_or,Bool.or_true,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
    all_goals simp only [routingAdjustedCell,frameOf,decide_false,decide_true,idx,Lv,b,Nat.reduceBEq,
      Bool.false_and,Bool.true_and,Bool.not_true,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true]
    all_goals try rfl
    all_goals simp only [frameCell,frameOf,decide_false,iL,iH,sV,sRID,fs,idx,Lv,iB,b,vB,
      Nat.reduceEqDiff,decide_true,decide_false,Bool.false_or,Bool.or_false,Bool.true_or,Bool.or_true,
      Bool.false_eq_true,ite_true,ite_false]
    all_goals try rfl
    all_goals try simp only [nativeFieldByte,regStates,sV,sP,sRID,List.mem_cons,List.not_mem_nil,or_false,
      sPL,sVL,sSL,sGP,sDEP,sXP0,sXRI,sXG,sXST,sXL0,sXLH,sXRH,sXRF,sXRZ,
      Nat.reduceEqDiff,ite_false]
    all_goals try rfl
    all_goals split <;> simp_all only [decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false]
  · rw [routingAdjusted_scratch _ _ _ col hh]
    exact routingAux_transport interval constants pub digests tokens fallback p ⟨sRID,0,len⟩ col
      (by rfl) hh


end ZkFormal.NearV3.Assembly.RcptSkeleton
