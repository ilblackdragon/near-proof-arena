import ZkFormal.NearV3.Assembly.RcptDigestMetadataPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem booleanReceiptTrace_native_digest_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++digestMetadataConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx constants) pub digests (digestMetadata fallback) (digestHeaderMetadata headerFallback)) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_states hp own ctx lists hsource hw hne hflags hrun hgas
      constants pub digests (digestMetadata fallback) (digestHeaderMetadata headerFallback) hown pos hpos e he
  · exact booleanReceiptTrace_digestMetadata own ctx lists hw 22 pos (nativePriceConstants ctx constants)
      pub digests fallback headerFallback e he

set_option maxRecDepth 4096 in
theorem native_digest_checkpoint_count : (cRegs++cEmit++cStates++digestMetadataConstraints).length=642 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
