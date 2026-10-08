import ZkFormal.NearV3.Assembly.RcptNativeCharacters

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxRecDepth 8192 in
theorem character_receipt_cells (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hs : row.state∈[sP,sV,sS]) :
    ∀col,ZkFormal.Near.Render.RcptP.chCol col=true→
      receiptCell (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterAux fallback)))
        p row col=ZkFormal.Near.Render.RcptP.chRow (characterByte p row) row.state col := by
  intro col hc
  have hcol : col=6 ∨ col=8 ∨ col=12 ∨ col=30 ∨ col=111 ∨ col=112 ∨ col=113 ∨ col=114 ∨
      col=115 ∨ col=116 ∨ col=117 ∨ col=118 ∨ col=119 ∨ col=120 ∨ col=121 ∨ col=122 ∨ col=123 := by
    simp only [ZkFormal.Near.Render.RcptP.chCol,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    omega
  have hstate : row.state=sP ∨ row.state=sV ∨ row.state=sS := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hs
  rcases hstate with hstate|hstate|hstate <;>
    rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp (disch := decide) only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,boolInput,
      characterAux,ZkFormal.Near.Render.RcptP.chRow,controlCell,nativeFieldByte,characterByte,characterBytes,
      reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,boolCols,
      regStates,sP,sV,sS,sRID,sPK,sGP,sDEP,sPL,sVL,sSL,sT0,sKT,sTL,sXP0,sXG,sXST,sXL0,sXRH,sXRF,sXRZ,sXRI,sXLH,
      hstate,act,idx,fs,fe,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte]
  all_goals try rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
