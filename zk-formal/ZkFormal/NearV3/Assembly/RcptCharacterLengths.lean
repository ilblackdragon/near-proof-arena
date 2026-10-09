import ZkFormal.NearV3.Assembly.RcptCharacterComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RoutingBoundedLayout

/-- The two six-bit account-length witnesses share no columns with routing
comparisons, token windows, character metadata or digest-request metadata. -/
def characterLengthAux (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (col : Nat) : Fp :=
  if row.state∈[sP,sV,sS] then
    if xb 0≤col ∧ col<xb 6 then frameBit ((characterBytes p.input row.state).length-2) (col-xb 0)
    else if xb 6≤col ∧ col<xb 12 then frameBit (64-(characterBytes p.input row.state).length) (col-xb 6)
    else fallback p row col
  else fallback p row col

def characterLengthConstraints : List Expr :=
  [mul3 (c fe) (c sP) (sub (sub (c Lp) (k 2)) (bitsX 0 6)),
   mul3 (c fe) (c sV) (sub (sub (c Lv) (k 2)) (bitsX 0 6)),
   mul3 (c fe) (c sS) (sub (sub (c Ls) (k 2)) (bitsX 0 6)),
   mul3 (c fe) (c sP) (sub (sub (k 64) (c Lp)) (bitsX 6 6)),
   mul3 (c fe) (c sV) (sub (sub (k 64) (c Lv)) (bitsX 6 6)),
   mul3 (c fe) (c sS) (sub (sub (k 64) (c Ls)) (bitsX 6 6))]

set_option maxRecDepth 4096 in
theorem characterLengthConstraints_shape : characterLengthConstraints.length=6 ∧
    characterLengthConstraints.all currentExpr=true ∧ characterLengthConstraints.all noEmissionExpr=true := by decide

theorem characterBytes_bounds (x : Input) (hw : x.receipt.wf=true) (s : Nat)
    (hs : s∈[sP,sV,sS]) : 2≤(characterBytes x s).length ∧ (characterBytes x s).length≤64 := by
  have hh := characterBytes_valid x hw s hs
  simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact hh.1

theorem characterLength_bit_cells (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (hs : row.state∈[sP,sV,sS]) (i : Nat) (hi : i<6) :
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row (xb i)=
        frameBit ((characterBytes p.input row.state).length-2) i ∧
    receiptCell (booleanConstants constants)
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux (characterLengthAux fallback))) p row (xb (6+i))=
        frameBit (64-(characterBytes p.input row.state).length) i := by
  have hh : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  have hnot : row.state≠sGP := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,sP,sV,sS] at hs
    unfold sGP
    omega
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [receiptCell,tokenReceiptAux,streamAux,tokenAux,booleanReceiptAux,characterLengthAux,
      reg,tok,xb,b,rf,rl,lastR,le,j,nj,r,cj,o,oEnd,o2,o2End,Lp,Lv,Ls,kt,hr,rconsts,
      kslot,tprev,ge,big,sys,ee,gq,dm,dd,q,Nat.reduceAdd,Nat.reduceLT,Nat.reduceLeDiff,Nat.reduceEqDiff,
      hs,hnot,List.mem_cons,List.not_mem_nil,or_false,true_or,false_or,or_true,or_false,
      and_true,and_false,true_and,false_and,decide_false,decide_true,Bool.false_or,Bool.or_false,
      Bool.true_or,Bool.or_true,Bool.false_eq_true,↓reduceIte,Nat.reduceSub]
  all_goals constructor <;> exact boolInput_preserves _ _ (frameBit_boolean _ _)

theorem characterLengthConstraints_in_chars : ∀e∈characterLengthConstraints,e∈cChars := by
  intro e he
  simp only [characterLengthConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
