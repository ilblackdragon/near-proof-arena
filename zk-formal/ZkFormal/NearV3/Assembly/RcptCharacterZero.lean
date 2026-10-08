import ZkFormal.NearV3.Assembly.RcptCharacterCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def characterZeroColumn (col : Nat) : Bool := col==sP || col==sV || col==sS || decide (111≤col ∧ col≤123)

set_option maxRecDepth 4096 in
theorem charLocalConstraints_zero_shape :
    charLocalConstraints.all (ZkFormal.Near.Render.RcptP.Zr characterZeroColumn (fun _=>false) false)=true := by decide

set_option maxRecDepth 8192 in
theorem character_receipt_nonstring (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hs : row.state∉[sP,sV,sS]) :
    ∀col,characterZeroColumn col=true→
      receiptCell (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterAux fallback)))
        p row col=0 := by
  intro col hc
  have hp : row.state≠6 ∧ row.state≠8 ∧ row.state≠12 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,sP,sV,sS] at hs
    omega
  have hcol : col=6 ∨ col=8 ∨ col=12 ∨ col=111 ∨ col=112 ∨ col=113 ∨ col=114 ∨
      col=115 ∨ col=116 ∨ col=117 ∨ col=118 ∨ col=119 ∨ col=120 ∨ col=121 ∨ col=122 ∨ col=123 := by
    simp only [characterZeroColumn,sP,sV,sS,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    omega
  rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp (disch := decide) only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,boolInput,
      characterAux,controlCell,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,boolCols,kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,
      act,idx,fs,fe,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      hs,List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte]
  all_goals try rfl
  all_goals split <;> simp_all

set_option maxRecDepth 8192 in
theorem character_header_cells (own : Nat) (before : ListPlan→Nat)
    (fallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat) :
    ∀col,characterZeroColumn col=true→
      headerCell (headerStreamAux own before
        (emissionHeaderFallback (booleanHeaderAux (characterHeaderAux fallback)))) p ⟨sCL,i,12⟩ col=0 := by
  intro col hc
  have hcol : col=6 ∨ col=8 ∨ col=12 ∨ col=111 ∨ col=112 ∨ col=113 ∨ col=114 ∨
      col=115 ∨ col=116 ∨ col=117 ∨ col=118 ∨ col=119 ∨ col=120 ∨ col=121 ∨ col=122 ∨ col=123 := by
    simp only [characterZeroColumn,sP,sV,sS,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at hc
    omega
  rcases hcol with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
