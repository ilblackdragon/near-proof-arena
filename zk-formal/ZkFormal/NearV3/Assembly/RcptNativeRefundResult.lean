import ZkFormal.NearV3.Assembly.RcptNativeFlags

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- Exact ordinary-branch refund output, with the renderer's native flag. -/
theorem applyReceipt_refunds (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (hs : (r.predecessorId == AccountId.system)=false)
    (h : applyReceipt ⟨ctx.height,ctx.gasPrice⟩ st r=some out) :
    out.refunds=st.refunds++
      (if nativeRefund ctx r then [gasRefundReceipt r ctx.height (nativeSurplus ctx r)] else []) := by
  unfold applyReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); split at h)
    | (simp only [Option.some.injEq] at h; subst out))
  all_goals simp only [nativeRefund,hs,Bool.not_false,Bool.true_and,nativeSurplus]
  all_goals split <;> simp_all

/-- The system branch preserves the refund sequence. -/
theorem applySystemReceipt_refunds (st out : Acc) (r : Receipt)
    (h : applySystemReceipt st r=.ok out) : out.refunds=st.refunds := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure] at h); split at h)
    | (simp only [Except.ok.injEq] at h; subst out; rfl))

end ZkFormal.NearV3.Assembly.RcptSkeleton
