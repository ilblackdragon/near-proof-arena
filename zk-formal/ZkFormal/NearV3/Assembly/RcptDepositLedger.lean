import ZkFormal.NearV3.Assembly.RcptDepositArithmetic
import ZkFormal.NearV3.Assembly.RcptGasProductNativeBounds

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

structure NativeDepositStep where
  before : Acc
  receipt : Receipt
  account : Account
  after : Acc

def nativeReceiptStep (ctx : ApplyCtx) (st : Acc) (r : Receipt) : Option Acc :=
  if r.predecessorId==AccountId.system then
    match applySystemReceipt st r with
    | .ok out=>some out
    | .error _=>none
  else applyReceipt ⟨ctx.height,ctx.gasPrice⟩ st r

def nativeDepositLedger (ctx : ApplyCtx) : Acc→List Receipt→Option (List NativeDepositStep)
  | _,[]=>some []
  | st,r::rs=>do
      let a←nativeBalanceAccount st r
      let out←nativeReceiptStep ctx st r
      let rest←nativeDepositLedger ctx out rs
      pure (⟨st,r,a,out⟩::rest)

def NativeDepositStep.Valid (ctx : ApplyCtx) (s : NativeDepositStep) : Prop :=
  NativeBalanceData s.before s.receipt s.account ∧ nativeReceiptStep ctx s.before s.receipt=some s.after

theorem nativeReceiptStep_balance_data (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (h : nativeReceiptStep ctx st r=some out) : ∃a,NativeBalanceData st r a := by
  unfold nativeReceiptStep at h
  split at h
  · cases ha : applySystemReceipt st r with
    | error e=>simp only [ha] at h;cases h
    | ok out'=>
      simp only [ha,Option.some.injEq] at h
      subst out
      exact applySystemReceipt_balance_data st out' r ha
  · exact applyReceipt_balance_data _ st out r h

theorem nativeDepositLedger_cons (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (rs : List Receipt) (a : Account) (rest : List NativeDepositStep)
    (ha : NativeBalanceData st r a) (hs : nativeReceiptStep ctx st r=some out)
    (hr : nativeDepositLedger ctx out rs=some rest) :
    nativeDepositLedger ctx st (r::rs)=some (⟨st,r,a,out⟩::rest) := by
  simp only [nativeDepositLedger,nativeBalanceAccount_of_data ha,hs,hr,bind,Option.bind,pure]

/-- Account reads are taken from each actual runtime state, preserving order,
including the native system branch. No independent account-array premise. -/
theorem applyReceipts_deposit_ledger (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc×List Limit),
      applyReceipts ctx i st rs=.ok out→
      ∃steps,nativeDepositLedger ctx st.1 rs=some steps ∧
        steps.map NativeDepositStep.receipt=rs ∧ ∀s∈steps,s.Valid ctx
  | [],_,_,_,_=>by exact ⟨[],rfl,rfl,by simp⟩
  | r::rs,i,(acc,ls),out,h=>by
      simp only [applyReceipts] at h
      split at h
      · cases h
      · split at h
        · rename_i hr
          obtain ⟨acc',ha,h⟩ := Sched.bind_ok h
          obtain ⟨steps,hl,ho,hv⟩ := applyReceipts_deposit_ledger ctx rs (i+1) (acc',ls) out h
          obtain ⟨a,hd⟩ := applySystemReceipt_balance_data acc acc' r ha
          have hs : nativeReceiptStep ctx acc r=some acc' := by simp only [nativeReceiptStep,hr,ite_true,ha]
          refine ⟨⟨acc,r,a,acc'⟩::steps,nativeDepositLedger_cons ctx acc acc' r rs a steps hd hs hl,?_,?_⟩
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
            obtain ⟨steps,hl,ho,hv⟩ := applyReceipts_deposit_ledger ctx rs (i+1) (acc',ls') out h
            obtain ⟨a,hd⟩ := applyReceipt_balance_data _ acc acc' r ha
            have hs : nativeReceiptStep ctx acc r=some acc' := by simp only [nativeReceiptStep,hr,ite_false,ha,Bool.false_eq_true]
            refine ⟨⟨acc,r,a,acc'⟩::steps,nativeDepositLedger_cons ctx acc acc' r rs a steps hd hs hl,?_,?_⟩
            · simp only [List.map_cons,ho]
            · intro s hmem
              rcases List.mem_cons.mp hmem with rfl|hmem
              · exact ⟨hd,hs⟩
              · exact hv s hmem

/-- The ledger starts at the real post-scheduler trie and retains the exact
receipt order of successful native execution. -/
theorem applyNewChunk_deposit_ledger (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs=.ok out) :
    ∃mid so steps,schedStep prims ctx t=.ok (mid,so) ∧
      nativeDepositLedger ctx ⟨mid,[],[],0,0⟩ rs=some steps ∧
      steps.map NativeDepositStep.receipt=rs ∧ ∀s∈steps,s.Valid ctx := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := Sched.bind_ok h
  obtain ⟨_,_,h⟩ := Sched.bind_ok h
  obtain ⟨⟨mid,so⟩,hmid,h⟩ := Sched.bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := Sched.bind_ok h
  obtain ⟨_,_,h⟩ := Sched.bind_ok h
  obtain ⟨_,_,h⟩ := Sched.bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,_⟩ := Sched.bind_ok h
  obtain ⟨steps,hl,ho,hv⟩ := applyReceipts_deposit_ledger ctx rs 0 _ (acc,ls) ha
  exact ⟨mid,so,steps,hmid,hl,ho,hv⟩

theorem NativeDepositStep.arithmetic {ctx : ApplyCtx} {s : NativeDepositStep}
    (h : s.Valid ctx) : DepositArithmeticOk (nativeDepositData s.account s.receipt) :=
  nativeBalanceData_arithmetic h.1

end ZkFormal.NearV3.Assembly.RcptSkeleton
