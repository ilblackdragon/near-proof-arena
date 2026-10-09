import ZkFormal.NearV3.Assembly.RcptNamedScore
import ZkFormal.NearV3.Assembly.RcptPredecessorComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedAux (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  let d := characterData p.input.receipt
  if row.state=sV then
    if col=acc then Fp.ofNat (accV d row.index) else
    if col=vc0 then Fp.ofNat (d.recv.getD 0 0) else
    if col=vc1 then Fp.ofNat (d.recv.getD 1 0) else
    if col=h01 then Fp.ofNat (h01V d) else
    if col=p1 then Fp.ofNat (pV1 d) else
    if col=p2 then Fp.ofNat (pV2 d) else
    if col=p3 then Fp.ofNat (pV3 d) else
    if col=i1 then (Fp.ofNat (pV1 d))⁻¹ else
    if col=i2 then (Fp.ofNat (pV2 d))⁻¹ else
    if col=i3 then (Fp.ofNat (pV3 d))⁻¹ else fallback p row col
  else fallback p row col

theorem namedColumns_not_boolean (col : Nat) (hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]) :
    col∉boolCols := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

set_option maxRecDepth 4096 in
theorem namedAux_transport (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (col : Nat)
    (hc : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3]) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (namedAux fallback))) p row col=
        namedAux fallback p row col := by
  have hn := namedColumns_not_boolean col hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,
      acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,and_true,and_false,true_and,false_and,
      decide_false,decide_true,Bool.false_or,Bool.or_false,Bool.false_eq_true,↓reduceIte]
    exact if_neg hn

theorem named_predecessor_commute (fallback : ReceiptPlan→Coord→Nat→Fp) :
    namedAux (predecessorAux fallback)=predecessorAux (namedAux fallback) := by
  funext p row col
  by_cases hs : row.state=sV
  · have hp : row.state≠sP := by rw [hs];decide
    simp only [namedAux,predecessorAux,if_pos hs,if_neg hp]
  · simp only [namedAux,predecessorAux,if_neg hs]

end ZkFormal.NearV3.Assembly.RcptSkeleton
