import ZkFormal.NearV3.Candidates.ProcNativeForwardFold
import ZkFormal.NearV3.Assembly.RcptRefundLedger
namespace ZkFormal.NearV3.Candidates.ProcNativeForwardRuntime
open NearSpec NearSpecV3 NearSpec.TransferV1
open ZkFormal.NearV3.Assembly.RcptSkeleton ProcNativeForwardSize

private theorem bind_ok {α β : Type} {a : Except String α}
    {f : α→Except String β} {b : β} (h:a.bind f=.ok b) :
    ∃x,a=.ok x ∧ f x=.ok b := by cases a <;> simp_all [Except.bind]

/-- Actual receipt execution forwards exactly its ordered native refund ledger. -/
theorem receipts_forward (ctx : ApplyCtx) :
    ∀(rs : List Receipt) (i : Nat) (st out : Acc×List Limit),
      applyReceipts ctx i st rs=.ok out →
      forwardAll ctx st.2 (rs.flatMap (nativeRefunds ctx))=some out.2
  | [],_,st,out,h=>by cases h; rfl
  | r::rs,i,(acc,ls),out,h=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · rename_i hr
        obtain ⟨acc',ha,h⟩:=bind_ok h
        have hn:nativeRefunds ctx r=[] := by simp [nativeRefunds,nativeRefund,hr]
        have ho:=receipts_forward ctx rs (i+1) (acc',ls) out h
        simpa only [List.flatMap_cons,hn,List.nil_append] using ho
      · rename_i hr
        split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',hf,h⟩:=bind_ok h
          have he:=applyReceipt_refunds ctx acc acc' r
            (by simpa only [Bool.eq_false_iff] using hr) ha
          have hfirst:=ProcNativeForwardFold.fold_success ctx
            (acc'.refunds.drop acc.refunds.length) ls ls' hf
          have href:acc'.refunds.drop acc.refunds.length=nativeRefunds ctx r := by
            rw [he]
            simp [nativeRefunds]
          rw [href] at hfirst
          have ho:=receipts_forward ctx rs (i+1) (acc',ls') out h
          rw [List.flatMap_cons,ProcNativeForwardFold.append,hfirst]
          exact ho

/-- No forwarding premise is added: successful native execution itself supplies
forwardAll on precisely the appended suffix of the accumulator's refunds. -/
theorem appended_refunds (ctx : ApplyCtx) (rs : List Receipt) (i : Nat)
    (st out : Acc×List Limit) (h:applyReceipts ctx i st rs=.ok out) :
    forwardAll ctx st.2 (out.1.refunds.drop st.1.refunds.length)=some out.2 := by
  have he:=applyReceipts_refund_ledger ctx rs i st out h
  rw [he]
  simpa using receipts_forward ctx rs i st out h

/-- Native forwarding conservation for every shard, with exact capped byte charge. -/
theorem appended_sizes (ctx : ApplyCtx) (rs : List Receipt) (i : Nat)
    (st out : Acc×List Limit) (h:applyReceipts ctx i st rs=.ok out) (s : Nat) :
    (Limit.get out.2 s).size+
      (((out.1.refunds.drop st.1.refunds.length).filter fun r=>ctx.layout.shardOf r.receiverId==s).map
        fun r=>min r.encode.length maxReceiptSize).sum=(Limit.get st.2 s).size :=
  all_sizes ctx _ st.2 out.2 (appended_refunds ctx rs i st out h) s

theorem appended_demand_bound (ctx : ApplyCtx) (rs : List Receipt) (i : Nat)
    (st out : Acc×List Limit) (h:applyReceipts ctx i st rs=.ok out)
    (d : Nat×Nat) (hd:d∈fwdSizes ctx (out.1.refunds.drop st.1.refunds.length)) :
    d.2≤(Limit.get st.2 d.1).size :=
  demand_bound ctx _ st.2 out.2 (appended_refunds ctx rs i st out h) d hd
end ZkFormal.NearV3.Candidates.ProcNativeForwardRuntime
