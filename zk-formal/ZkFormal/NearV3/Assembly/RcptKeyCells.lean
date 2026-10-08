import ZkFormal.NearV3.Assembly.RcptKeyGates

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxRecDepth 4096 in
theorem keyAux_transport (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (tokens : ReceiptPlan→TokenInput) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : col∈[tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK]) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests tokens (booleanReceiptAux (keyAux accountId accessId fallback))) p row col=
      keyAux accountId accessId fallback p row col := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
      tA,tB,symA,symB,lastA,gKA,gKB,kz,gF,fkF,kF,gAK,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
      decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,ite_true,ite_false]
  all_goals first
    | exact if_neg (by decide)
    | exact boolInput_preserves _ _ (bitCell_boolean _)

end ZkFormal.NearV3.Assembly.RcptSkeleton
