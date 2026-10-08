import ZkFormal.NearV3.Assembly.RcptPredecessorScore

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def systemConstants (fallback : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) (col : Nat) : Fp :=
  if col=sys then bitCell (p.input.receipt.predecessorId==AccountId.system) else fallback p col

def predecessorAux (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state=sP then
    if col=acc then Fp.ofNat (accP (characterData p.input.receipt) row.index) else
    if col=p1 then Fp.ofNat (pP (characterData p.input.receipt)) else
    if col=isys then (Fp.ofNat (pP (characterData p.input.receipt)))⁻¹ else fallback p row col
  else fallback p row col

def predecessorConstraints : List Expr :=
  [mul3 (c sP) (c fs) (sub (c acc) (RcptV3.sq (sub (c b) (c (reg 0))))),
   mul3 (c sP) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) (RcptV3.sq (sub (n b) (n (reg 0)))))),
   mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (RcptV3.sq (sub (c Lp) (k 6))))),
   mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (Dsl.not (c sys))),
   .mul (mul3 (c sP) (c fe) (c sys)) (c p1),
   mul3 RcptV3.rowE (c sys) (sub (c Lp) (k 6))]

theorem predecessorConstraints_in_chars : ∀e∈predecessorConstraints,e∈cChars := by
  intro e he
  simp only [predecessorConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem systemConstants_cell (ctx : ApplyCtx) (constants : ReceiptPlan→Nat→Fp) (p : ReceiptPlan) :
    booleanConstants (nativePriceConstants ctx (systemConstants constants)) p sys=
      bitCell (p.input.receipt.predecessorId==AccountId.system) := by
  change boolInput sys (bitCell _)=_
  exact boolInput_preserves _ _ (bitCell_boolean _)

theorem predecessor_not_bool (col : Nat) (hc : col=acc ∨ col=p1 ∨ col=isys) : col∉boolCols := by
  rcases hc with rfl|rfl|rfl <;> decide

set_option maxRecDepth 4096 in
theorem predecessorAux_cells (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord) (hs : row.state=sP) :
    let cell := receiptCell (booleanConstants (nativePriceConstants ctx (systemConstants constants)))
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (predecessorAux fallback))) p row
    cell acc=Fp.ofNat (accP (characterData p.input.receipt) row.index) ∧
    cell p1=Fp.ofNat (pP (characterData p.input.receipt)) ∧
    cell isys=(Fp.ofNat (pP (characterData p.input.receipt)))⁻¹ ∧
    cell sys=bitCell (p.input.receipt.predecessorId==AccountId.system) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,predecessorAux,hs,
      acc,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sP,sGP,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte]
    exact if_neg (predecessor_not_bool _ (Or.inl rfl))
  · simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,predecessorAux,hs,
      acc,p1,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sP,sGP,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte]
    exact if_neg (predecessor_not_bool _ (Or.inr (Or.inl rfl)))
  · simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,predecessorAux,hs,
      acc,p1,isys,reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,sP,sGP,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte]
    exact if_neg (predecessor_not_bool _ (Or.inr (Or.inr rfl)))
  · exact systemConstants_cell ctx constants p

end ZkFormal.NearV3.Assembly.RcptSkeleton
