import ZkFormal.NearV3.Assembly.RcptNativeRefundResult
import ZkFormal.NearV3.Assembly.Compute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1 Sched

/-- Exact per-receipt native outcome, including system gas/token semantics and
the actual ordinary refund identifier. -/
def nativeOutcome (ctx : ApplyCtx) (r : Receipt) : Outcome :=
  { id:=r.receiptId,
    receiptIds:=if nativeRefund ctx r then
      [(gasRefundReceipt r ctx.height (nativeSurplus ctx r)).receiptId] else [],
    gasBurnt:=Params.G,
    tokensBurnt:=if r.predecessorId==AccountId.system then 0 else Params.G*min r.gasPrice ctx.gasPrice,
    executorId:=r.receiverId }

theorem applyReceipt_outcomes (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (hs : (r.predecessorId==AccountId.system)=false)
    (h : applyReceipt ⟨ctx.height,ctx.gasPrice⟩ st r=some out) :
    out.outcomes=st.outcomes++[nativeOutcome ctx r] := by
  unfold applyReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);split at h)
    | (simp only [Option.some.injEq] at h;subst out))
  all_goals simp only [nativeOutcome,nativeRefund,hs,Bool.not_false,Bool.true_and,nativeSurplus,↓reduceIte]
  all_goals split <;> simp_all

theorem applySystemReceipt_outcomes (ctx : ApplyCtx) (st out : Acc) (r : Receipt)
    (hs : (r.predecessorId==AccountId.system)=true)
    (h : applySystemReceipt st r=.ok out) :
    out.outcomes=st.outcomes++[nativeOutcome ctx r] := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);(try simp only [bind,Except.bind,pure,Except.pure] at h);split at h)
    | (simp only [Except.ok.injEq] at h;subst out;
        simp [nativeOutcome,nativeRefund,hs]))

/-- Ordered execution appends exactly one native outcome for every receipt;
system and ordinary branches share the same list identity. -/
theorem applyReceipts_outcomes (ctx : ApplyCtx) :
    ∀(rs : List Receipt)(i : Nat)(acc : Acc)(ls : List Limit)(out : Acc×List Limit),
      applyReceipts ctx i (acc,ls) rs=.ok out→
      out.1.outcomes=acc.outcomes++rs.map (nativeOutcome ctx)
  | [],_,_,_,_,h => by cases h;simp
  | r::rs,i,acc,ls,out,h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    split at h
    · rename_i hs
      obtain ⟨acc',ha,h⟩ := bind_ok h
      rw [applyReceipts_outcomes ctx rs (i+1) acc' ls out h,
        applySystemReceipt_outcomes ctx acc acc' r hs ha]
      simp only [List.map_cons,List.append_assoc,List.singleton_append]
    · rename_i hs
      have hs' : (r.predecessorId==AccountId.system)=false := Bool.eq_false_iff.mpr hs
      split at h
      · split at h <;> cases h
      · rename_i acc' ha
        obtain ⟨ls',_,h⟩ := bind_ok h
        rw [applyReceipts_outcomes ctx rs (i+1) acc' ls' out h,
          applyReceipt_outcomes ctx acc acc' r hs' ha]
        simp only [List.map_cons,List.append_assoc,List.singleton_append]

theorem applyNewChunk_outcomes (prims : Prims) {ctx : ApplyCtx} {t : PTrie}
    {rs : List Receipt} {out : MainOut} (h : applyNewChunk prims ctx t rs=.ok out) :
    out.outcomes=rs.map (nativeOutcome ctx) := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨_,so⟩,_,h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  cases h
  simpa using applyReceipts_outcomes ctx rs 0 _ _ _ ha

end ZkFormal.NearV3.Assembly.RcptSkeleton
