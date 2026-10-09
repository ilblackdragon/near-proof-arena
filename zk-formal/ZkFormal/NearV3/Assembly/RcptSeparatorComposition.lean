import ZkFormal.NearV3.Assembly.RcptSeparatorPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem booleanReceiptTrace_native_separator_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx constants) pub digests (digestMetadata (characterAux (characterLengthAux fallback))) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_length_checkpoint hp own ctx lists hsource hw hne hflags hrun hgas
      constants pub digests fallback headerFallback hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_separators own ctx lists hw 22 pos (nativePriceConstants ctx constants)
      pub digests (digestMetadata (characterLengthAux fallback)) (digestHeaderMetadata headerFallback)
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [character_digest_commute,character_digest_header_commute] using hh

set_option maxRecDepth 4096 in
theorem native_separator_checkpoint_count :
    (cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints).length=701 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
