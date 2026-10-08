import ZkFormal.NearV3.Assembly.RcptPlanLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Exact byte equality across consecutive generated receipt indices. -/
theorem receiptPlanToken_boundary (ctx : ApplyCtx) (lists : List (List Input))
    (lp : ListPlan) (hl : lp∈planLists 0 0 8 lists) (p : ReceiptPlan)
    (hp : p∈planReceipts lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList lp.inputs)
    (q : ReceiptPlan) (hq : q.receiptIndex=p.receiptIndex+1) :
    (receiptPlanToken ctx lists p).newBytes=(receiptPlanToken ctx lists q).oldBytes := by
  have hr : (lists.flatten.map Input.receipt)[p.receiptIndex]?=some p.input.receipt := by
    simp only [List.getElem?_map,global_plan_receipt lists lp hl p hp,Option.map_some]
  simp only [receiptPlanToken,TokenInput.newBytes,TokenInput.oldBytes,hq]
  rw [prefixBurn_succ ctx _ 0 _ _ hr]

def finalState (x : Input) : Nat := if x.refund then sXRZ else sXLH

theorem tokenOf_final (x : TokenInput) (input : Input) (i len j : Nat) :
    tokenOf x ⟨finalState input,i,len⟩ j=x.newBytes.getD j 0 := by
  cases h : input.refund <;> simp [finalState,h,tokenOf,sXRZ,sXLH,sGP]

theorem tokenOf_first (x : TokenInput) (i len j : Nat) :
    tokenOf x ⟨sPL,i,len⟩ j=x.oldBytes.getD j 0 := rfl

/-- The actual token carry polynomials at a receipt boundary, with totals
constructed from native input order rather than supplied as an equality premise. -/
theorem receipt_boundary_token_carry (ctx : ApplyCtx) (lists : List (List Input))
    (lp : ListPlan) (hl : lp∈planLists 0 0 8 lists) (p : ReceiptPlan)
    (hp : p∈planReceipts lp.listIndex lp.inputs.length lp.receiptIndex 1 12 lp.bodyOffset lp.lastList lp.inputs)
    (q : ReceiptPlan) (hq : q.receiptIndex=p.receiptIndex+1)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (i len nextLen : Nat) :
    ∀e∈carryTokenConstraints,e.eval
      ⟨fun _=>1,fun _ pos col=>if pos=0 then
        receiptCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
          p ⟨finalState p.input,i,len⟩ col
        else receiptCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
          q ⟨sPL,0,nextLen⟩ col⟩ 0 0 pub=0 := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  have hj' := List.mem_range.mp hj
  simp only [eval_mul,eval_sub,eval_c,eval_n]
  change _*(receiptCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
    q ⟨sPL,0,nextLen⟩ (tok j)-
    receiptCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
    p ⟨finalState p.input,i,len⟩ (tok j))=0
  rw [receipt_token_cell _ _ _ _ _ _ _ j hj',receipt_token_cell _ _ _ _ _ _ _ j hj',
    tokenOf_first,tokenOf_final,receiptPlanToken_boundary ctx lists lp hl p hp q hq]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
