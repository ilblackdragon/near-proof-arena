import ZkFormal.NearV3.Assembly.RcptCurrentFamily

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptEndConstraint : Expr :=
  sub (c rl) (.mul (c fe) (.add (c sXRZ) (.mul (c sXLH) (Dsl.not (c hr)))))

theorem receiptEndConstraint_footprint : currentExpr receiptEndConstraint=true ∧
    noEmissionExpr receiptEndConstraint=true := by decide

set_option maxRecDepth 4096 in
theorem receipt_endFlag (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (pub : List Fp) :
    receiptEndConstraint.eval (receiptPair constants aux p row row) 0 0 pub=0 := by
  have hrl : (receiptPair constants aux p row row).cell 0 0 rl=bitCell (receiptEnd p row) := rfl
  have hfe : (receiptPair constants aux p row row).cell 0 0 fe=if row.index+1=row.length then 1 else 0 := receipt_control_cell constants aux p row (c:=fe) (by decide)
  have hx : (receiptPair constants aux p row row).cell 0 0 sXRZ=if sXRZ=row.state then 1 else 0 :=
    (receipt_control_cell constants aux p row (c:=sXRZ) (by decide)).trans (control_state row (by decide))
  have hl : (receiptPair constants aux p row row).cell 0 0 sXLH=if sXLH=row.state then 1 else 0 :=
    (receipt_control_cell constants aux p row (c:=sXLH) (by decide)).trans (control_state row (by decide))
  have hr : (receiptPair constants aux p row row).cell 0 0 RcptV3.hr=if p.input.refund then 1 else 0 := rfl
  have hne : ¬(sXRZ=row.state ∧ sXLH=row.state) := by unfold sXRZ sXLH;omega
  simp only [receiptEndConstraint,eval_sub,eval_mul,eval_add,eval_c,eval_not,hrl,hfe,hx,hl,hr,bitCell,receiptEnd]
  by_cases hrefund : p.input.refund=true <;>
    by_cases he : row.index+1=row.length <;> by_cases hex : sXRZ=row.state <;> by_cases hel : sXLH=row.state <;>
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true,Bool.eq_false_iff,hrefund,he,hex,hel,show (row.state=sXRZ)=(sXRZ=row.state) from propext eq_comm,show (row.state=sXLH)=(sXLH=row.state) from propext eq_comm,↓reduceIte,and_true,and_false,true_and,false_and,or_true,or_false,true_or,false_or,not_true_eq_false,not_false_eq_true] <;> grind only

theorem header_endFlag (aux : ListPlan→Coord→Nat→Fp) (p : ListPlan) (i : Nat) (pub : List Fp) :
    receiptEndConstraint.eval (⟨fun _=>1,fun _ _ col=>headerCell aux p ⟨sCL,i,12⟩ col⟩ : Trace Fp) 0 0 pub=0 := by
  have hr : headerCell aux p ⟨sCL,i,12⟩ rl=0 := rfl
  have hx : headerCell aux p ⟨sCL,i,12⟩ sXRZ=0 := rfl
  have hl : headerCell aux p ⟨sCL,i,12⟩ sXLH=0 := rfl
  simp only [receiptEndConstraint,eval_sub,eval_mul,eval_add,eval_c,eval_not]
  change _=0
  simp only [hr,hx,hl]
  grind only

theorem booleanReceiptTrace_endFlag (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    receiptEndConstraint.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ receiptEndConstraint_footprint.2]
  apply plannedTrace_current_family lists hw log pos _ _ _ pub [receiptEndConstraint] (by decide)
    (fun p row _ _ e he=>by simp only [List.mem_singleton] at he;subst e;exact receipt_endFlag _ _ p row pub)
    (fun p i e he=>by simp only [List.mem_singleton] at he;subst e;exact header_endFlag _ p i pub) ?_ _ (by simp)
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  simp only [receiptEndConstraint,eval_sub,eval_mul,eval_add,eval_c,eval_not,zeroCurrentTrace]
  grind only

theorem receiptEndConstraint_in_states : receiptEndConstraint∈cStates := by
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  simp [receiptEndConstraint]

theorem booleanReceiptTrace_flags_checkpoint (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit++booleanConstraints++continuationConstraints++lastIndexConstraints++boundaryResetConstraints++successorConstraints++receiptFirstConstraints++[receiptEndConstraint],
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    · exact booleanReceiptTrace_structural_checkpoint own ctx lists hw log constants pub digests fallback headerFallback hcap hown pos hp e he
    · exact booleanReceiptTrace_firstFlags own ctx lists hw log pos constants pub digests fallback headerFallback e he
  · simp only [List.mem_singleton] at he
    subst e
    exact booleanReceiptTrace_endFlag own ctx lists hw log pos constants pub digests fallback headerFallback

end ZkFormal.NearV3.Assembly.RcptSkeleton
