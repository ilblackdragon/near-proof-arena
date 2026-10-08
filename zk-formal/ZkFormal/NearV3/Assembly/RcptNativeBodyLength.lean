import ZkFormal.NearV3.Assembly.RcptRefundLedger
import ZkFormal.NearV3.Assembly.RcptFinalPublic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

theorem nativeRefunds_length (ctx : ApplyCtx) (x : Input)
    (hw : x.receipt.wf=true) (hf : x.refund=nativeRefund ctx x.receipt) :
    ((nativeRefunds ctx x.receipt).map (fun r=>r.encode.length)).sum=refundLength x := by
  have hh := refundLength_native x hw ctx.height (nativeSurplus ctx x.receipt)
  rw [hf] at hh
  unfold nativeRefunds
  split <;> simp_all

/-- The planned body endpoint is the exact serialized native outgoing body,
not merely a chosen polynomial endpoint. -/
theorem applyNewChunk_planned_body_length (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hf : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (h : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out) :
    (u32 0++encodeReceipts out.outgoing).length=8+(lists.flatten.map refundLength).sum := by
  rw [applyNewChunk_refund_ledger ctx t _ out h]
  have hsum : ∀xs : List Input,(∀x∈xs,x.receipt.wf=true)→
      (∀x∈xs,x.refund=nativeRefund ctx x.receipt)→
      (((xs.map Input.receipt).flatMap (nativeRefunds ctx)).map (fun r=>r.encode.length)).sum=
        (xs.map refundLength).sum := by
    intro xs hw hf
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons,List.flatMap_cons,List.map_append,List.sum_append,List.sum_cons]
      rw [nativeRefunds_length ctx x (hw x (by simp)) (hf x (by simp)),
        ih (fun y hy=>hw y (by simp [hy])) (fun y hy=>hf y (by simp [hy]))]
  have hh := hsum lists.flatten
    (by intro x hx;obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx;exact hw xs hxs x hx)
    (by intro x hx;obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx;exact hf xs hxs x hx)
  have hc : ∀xs : List Bytes,(concatAll xs).length=(xs.map List.length).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [concatAll,List.length_append,List.map_cons,List.sum_cons,ih]
  simp only [encodeReceipts,List.length_append,hc,List.map_map,Function.comp_def,u32,leN,
    List.length_cons,List.length_nil]
  rw [hh]
  omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
