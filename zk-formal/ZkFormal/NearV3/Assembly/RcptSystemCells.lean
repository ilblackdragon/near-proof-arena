import ZkFormal.NearV3.Assembly.RcptSystemFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxRecDepth 4096 in
theorem systemAux_transport (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : col∈[gV,gS,sx,invD,scnt,invL]) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))) p row col=
        systemAux fallback p row col := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
      gV,gS,sx,invD,scnt,invL,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
      decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,↓reduceIte]
  · change boolInput gV (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  · change boolInput gS (bitCell _)=_
    exact boolInput_preserves _ _ (bitCell_boolean _)
  · exact if_neg (show sx∉boolCols by decide)
  · exact if_neg (show invD∉boolCols by decide)
  · exact if_neg (show scnt∉boolCols by decide)
  · exact if_neg (show invL∉boolCols by decide)

theorem systemAux_invL (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    systemAux fallback p row invL=(Fp.ofNat p.input.receipt.signerId.length-Fp.ofNat p.input.receipt.receiverId.length)⁻¹ := by
  simp only [systemAux,invL,gV,gS,sx,invD,scnt,Nat.reduceEqDiff,↓reduceIte]

theorem systemAux_invD (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) :
    systemAux fallback p row invD=(Fp.ofNat ((p.input.receipt.signerId.getD row.index 0).toNat)-
      Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat))⁻¹ := by
  simp only [systemAux,invL,gV,gS,sx,invD,scnt,Nat.reduceEqDiff,↓reduceIte]

end ZkFormal.NearV3.Assembly.RcptSkeleton
