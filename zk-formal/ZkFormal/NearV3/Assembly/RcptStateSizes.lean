import ZkFormal.NearV3.Assembly.RcptNativeCapacity

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptSizeConstraints : List Expr :=
  [.mul rowE (sub (c oEnd) (.add (c o) (.add (k 123) varE))),
   .mul rowE (sub (c o2End) (.add (c o2) (.mul (c hr) (sum [k 129,smul 2 (c Ls),smul 32 (c kt)]))))]

theorem receiptSizeConstraints_footprint : receiptSizeConstraints.all currentExpr=true ∧
    receiptSizeConstraints.all noEmissionExpr=true := by decide

theorem receiptSizeConstraints_in_states : ∀e∈receiptSizeConstraints,e∈cStates := by
  intro e he
  simp only [receiptSizeConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

set_option maxRecDepth 4096 in
theorem receipt_size_offsets (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (pub : List Fp) :
    ∀e∈receiptSizeConstraints,e.eval (receiptPair constants aux p row row) 0 0 pub=0 := by
  have hrc : (sub (c oEnd) (.add (c o) (.add (k 123) varE))).eval
      (receiptPair constants aux p row row) 0 0 pub=0 := by
    simp only [eval_sub,eval_add,eval_c,eval_k,varE,eval_sum_cons,eval_sum_nil,eval_smul]
    change ((p.rcOffset+rcLength p.input:Nat):Fp)-
      ((p.rcOffset:Fp)+(123+((p.input.receipt.predecessorId.length:Fp)+
        ((p.input.receipt.receiverId.length:Fp)+((p.input.receipt.signerId.length:Fp)+(32*(p.input.receipt.signerPk.tag:Fp)+0))))))=0
    unfold rcLength
    grind only
  have href : (sub (c o2End) (.add (c o2) (.mul (c hr) (sum [k 129,smul 2 (c Ls),smul 32 (c kt)])))).eval
      (receiptPair constants aux p row row) 0 0 pub=0 := by
    simp only [eval_sub,eval_add,eval_c,eval_mul,eval_k,eval_sum_cons,eval_sum_nil,eval_smul]
    change ((p.bodyOffset+refundLength p.input:Nat):Fp)-
      ((p.bodyOffset:Fp)+(if p.input.refund then (1:Fp) else 0)*(129+(2*(p.input.receipt.signerId.length:Fp)+(32*(p.input.receipt.signerPk.tag:Fp)+0))))=0
    unfold refundLength
    by_cases hh : p.input.refund=true <;> simp only [hh,↓reduceIte] <;> grind only
  intro e he
  simp only [receiptSizeConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> simp only [eval_mul,hrc,href] <;> grind only

theorem header_size_offsets (aux : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat) (pub : List Fp) :
    ∀e∈receiptSizeConstraints,e.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
  have hrow : rowE.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
    simp only [rowE,eval_sub,eval_c]
    change (1:Fp)-1=0
    grind only
  intro e he
  simp only [receiptSizeConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> simp only [eval_mul,hrow] <;> grind only

theorem booleanReceiptTrace_sizes (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈receiptSizeConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp receiptSizeConstraints_footprint.2 e he)]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub receiptSizeConstraints receiptSizeConstraints_footprint.1
    (fun p row _ _=>receipt_size_offsets _ _ p row pub) (fun p i=>header_size_offsets _ p i pub) ?_ e he
  intro e he
  have hzero : rowE.eval zeroCurrentTrace 0 0 pub=0 := by simp only [rowE,eval_sub,eval_c,zeroCurrentTrace];grind only
  simp only [receiptSizeConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl <;> simp only [eval_mul,hzero] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
