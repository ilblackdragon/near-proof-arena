import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLedgerPrefix
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 NearSpec.TransferV1 ZkFormal.Near Assembly Assembly.RcptSkeleton

def ledgerFinal : Acc→List NativeDepositStep→Acc
  | st,[]=>st
  | _,s::ss=>ledgerFinal s.after ss

theorem applyReceipts_deposit_ledger_final (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc×List Limit),
      applyReceipts ctx i st rs=.ok out→
      ∃steps,nativeDepositLedger ctx st.1 rs=some steps ∧
        steps.map NativeDepositStep.receipt=rs ∧ ledgerFinal st.1 steps=out.1 ∧ ∀s∈steps,s.Valid ctx
  | [],_,st,out,h=>by cases h;exact ⟨[],rfl,rfl,rfl,by simp⟩
  | r::rs,i,(acc,ls),out,h=>by
      simp only [applyReceipts] at h
      split at h
      · cases h
      · split at h
        · rename_i hr
          obtain ⟨acc',ha,h⟩ := Sched.bind_ok h
          obtain ⟨steps,hl,ho,hf,hv⟩ := applyReceipts_deposit_ledger_final ctx rs (i+1) (acc',ls) out h
          obtain ⟨a,hd⟩ := applySystemReceipt_balance_data acc acc' r ha
          have hs : nativeReceiptStep ctx acc r=some acc' := by simp only [nativeReceiptStep,hr,ite_true,ha]
          refine ⟨⟨acc,r,a,acc'⟩::steps,nativeDepositLedger_cons ctx acc acc' r rs a steps hd hs hl,?_,hf,?_⟩
          · simp only [List.map_cons,ho]
          · intro s hmem
            rcases List.mem_cons.mp hmem with rfl|hmem
            · exact ⟨hd,hs⟩
            · exact hv s hmem
        · rename_i hr
          split at h
          · split at h <;> cases h
          · rename_i acc' ha
            obtain ⟨ls',_,h⟩ := Sched.bind_ok h
            obtain ⟨steps,hl,ho,hf,hv⟩ := applyReceipts_deposit_ledger_final ctx rs (i+1) (acc',ls') out h
            obtain ⟨a,hd⟩ := applyReceipt_balance_data _ acc acc' r ha
            have hs : nativeReceiptStep ctx acc r=some acc' := by simp only [nativeReceiptStep,hr,ite_false,ha,Bool.false_eq_true]
            refine ⟨⟨acc,r,a,acc'⟩::steps,nativeDepositLedger_cons ctx acc acc' r rs a steps hd hs hl,?_,hf,?_⟩
            · simp only [List.map_cons,ho]
            · intro s hmem
              rcases List.mem_cons.mp hmem with rfl|hmem
              · exact ⟨hd,hs⟩
              · exact hv s hmem


theorem nativeDepositLedger_final_run {ctx : ApplyCtx} {st : Acc} {rs : List Receipt}
    {steps : List NativeDepositStep} (h:nativeDepositLedger ctx st rs=some steps)
    (hv:∀s∈steps,s.Valid ctx) :
    AccountWriteRun st.trie (steps.map ledgerWrite) (ledgerFinal st steps).trie := by
  induction rs generalizing st steps with
  | nil=>simp [nativeDepositLedger] at h;subst steps;exact .nil _
  | cons r rs ih=>
    simp only [nativeDepositLedger] at h
    cases ha:nativeBalanceAccount st r with
    | none=>simp [ha] at h
    | some a=>
      cases ho:nativeReceiptStep ctx st r with
      | none=>simp [ha,ho] at h
      | some out=>
        cases ht:nativeDepositLedger ctx out rs with
        | none=>simp [ha,ho,ht] at h
        | some tail=>
          simp only [ha,ho,ht,bind,Option.bind,pure,Option.some.injEq] at h
          subst steps
          exact .cons (ledger_account_write (hv (⟨st,r,a,out⟩ : NativeDepositStep) (by simp))) (ih ht (fun s hs=>hv s (by simp [hs])))

/-- Reuses the caller's ledger; successful native execution fixes its actual
final accumulator, including the empty-receipt case. -/
theorem nativeDepositLedger_final_state {ctx : ApplyCtx} {rs : List Receipt} {i : Nat}
    {st out : Acc×List Limit} (h:applyReceipts ctx i st rs=.ok out)
    {steps : List NativeDepositStep} (hl:nativeDepositLedger ctx st.1 rs=some steps) :
    ledgerFinal st.1 steps=out.1 := by
  obtain ⟨ss,hs,_,hf,_⟩:=applyReceipts_deposit_ledger_final ctx rs i st out h
  have he:ss=steps:=Option.some.inj (hs.symm.trans hl)
  simpa only [he] using hf

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
