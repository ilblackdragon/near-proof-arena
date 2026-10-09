import ZkFormal.NearV3.Assembly.RcptPredecessorCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem booleanReceiptTrace_predecessor (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log) :
    ∀e∈predecessorConstraints,e.eval
      (booleanReceiptTrace own ctx lists log (nativePriceConstants ctx (systemConstants constants))
        pub digests (predecessorAux fallback) headerFallback) 0 pos pub=0 := by
  intro e he
  have hh : e∈predecessorCurrentConstraints ∨ e=predecessorStepConstraint := by
    simp only [predecessorConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
    simp only [predecessorCurrentConstraints,predecessorStepConstraint,List.mem_cons,List.not_mem_nil,or_false]
    grind only
  rcases hh with hh|rfl
  · exact booleanReceiptTrace_predecessorCurrent own ctx lists hw log pos constants pub digests fallback headerFallback e hh
  · exact booleanReceiptTrace_predecessorStep own ctx lists log pos constants pub digests fallback headerFallback hcap

theorem booleanReceiptTrace_native_predecessor_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants constants)) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux fallback)))) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_separator_checkpoint hp own ctx lists hsource hw hne hflags hrun hgas
      (systemConstants constants) pub digests (predecessorAux fallback) headerFallback hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_predecessor own ctx lists hw 22 pos constants pub digests
      (digestMetadata (characterAux (characterLengthAux fallback)))
      (digestHeaderMetadata (characterHeaderAux headerFallback))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [predecessor_digest_commute,predecessor_character_commute,predecessor_length_commute] using hh

set_option maxRecDepth 4096 in
theorem native_predecessor_checkpoint_count :
    (cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints).length=707 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
