import ZkFormal.NearV3.Assembly.RcptNativeRefundLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

/-- All state, register and emission polynomials on one physical trace. The
remaining arithmetic, account/key, routing and finalization families are not
asserted by this theorem. -/
theorem booleanReceiptTrace_native_states {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx constants) pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hpos e he
  have hc := booleanReceiptTrace_native_state_checkpoint hp own ctx lists hsource hw hne hrun hgas
    (nativePriceConstants ctx constants) pub digests fallback headerFallback hown pos hpos
  rcases List.mem_append.mp he with he|he
  · apply hc
    simp only [nativeStateCheckpointConstraints,headerCheckpointConstraints,stateCheckpointConstraints,List.mem_append]
    rcases List.mem_append.mp he with he|he
    · grind only
    · grind only
  · rcases cStates_checkpoint_coverage e he with he|he
    · exact hc e he
    · subst e
      exact booleanReceiptTrace_nativeRefund own ctx lists hflags 22 pos constants pub digests fallback headerFallback

set_option maxRecDepth 4096 in
theorem native_states_count : (cRegs++cEmit++cStates).length=637 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
