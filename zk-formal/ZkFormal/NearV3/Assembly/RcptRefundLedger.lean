import ZkFormal.NearV3.Assembly.RcptNativeRefundResult

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

def nativeRefunds (ctx : ApplyCtx) (r : Receipt) : List Receipt :=
  if nativeRefund ctx r then [gasRefundReceipt r ctx.height (nativeSurplus ctx r)] else []

private theorem refund_bind_ok {α β : Type} {a : Except String α}
    {f : α→Except String β} {b : β} (h : a.bind f=.ok b) :
    ∃x,a=.ok x ∧ f x=.ok b := by cases a <;> simp_all [Except.bind]

/-- Ordered native refunds, preserving all incoming receipts including system
receipts. Forwarding checks can reject, but never reorder the accepted list. -/
theorem applyReceipts_refund_ledger (ctx : ApplyCtx) :
    ∀(rs : List Receipt) (i : Nat) (st out : Acc×List Limit),
      applyReceipts ctx i st rs=.ok out→
      out.1.refunds=st.1.refunds++rs.flatMap (nativeRefunds ctx)
  | [],_,st,out,h=>by cases h;simp
  | r::rs,i,(acc,ls),out,h=>by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · rename_i hr
        obtain ⟨acc',ha,h⟩ := refund_bind_ok h
        have he := applySystemReceipt_refunds acc acc' r ha
        have hn : nativeRefunds ctx r=[] := by simp [nativeRefunds,nativeRefund,hr]
        have ho := applyReceipts_refund_ledger ctx rs (i+1) (acc',ls) out h
        simpa [List.flatMap_cons,hn,he] using ho
      · rename_i hr
        split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := refund_bind_ok h
          have he := applyReceipt_refunds ctx acc acc' r (by simpa only [Bool.eq_false_iff] using hr) ha
          have ho := applyReceipts_refund_ledger ctx rs (i+1) (acc',ls') out h
          simpa only [List.flatMap_cons,he,nativeRefunds,List.append_assoc] using ho

theorem applyNewChunk_refund_ledger (ctx : ApplyCtx) (t : PTrie) (rs : List Receipt)
    (out : MainOut) (h : applyNewChunk prims ctx t rs=.ok out) :
    out.outgoing=rs.flatMap (nativeRefunds ctx) := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨⟨mid,so⟩,_,h⟩ := refund_bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := refund_bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  obtain ⟨_,_,h⟩ := refund_bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  simpa using applyReceipts_refund_ledger ctx rs 0 _ (acc,ls) ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
