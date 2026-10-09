import ZkFormal.NearV3.Assembly.RcptNamedCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

/-- Discharges named-input evidence from the unchanged parsed source witness
and exact applied receipt order. No receipt domain restriction is added. -/
theorem appliedInputs_named {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hd : decodeStateWitness bs=.ok w) (lists : List (List Input))
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w) :
    ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true := by
  intro xs hxs x hx
  apply appliedReceipts_named hd
  rw [←hls]
  exact List.mem_map.mpr ⟨x,List.mem_flatten.mpr ⟨xs,hxs,hx⟩,rfl⟩

theorem booleanReceiptTrace_native_named_inverse_checkpoint {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints++namedInverseConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants constants)) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux fallback))))) (digestHeaderMetadata (characterHeaderAux headerFallback))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_predecessor_checkpoint hp own ctx lists hsource hw hne hflags hrun hgas
      constants pub digests (namedAux fallback) headerFallback hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_namedInverse own ctx lists hw hn 22 pos
      (nativePriceConstants ctx (systemConstants constants)) pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux fallback))))
      (digestHeaderMetadata (characterHeaderAux headerFallback)) e he
    simpa only [named_digest_commute,named_character_commute,named_length_commute,named_predecessor_commute] using hh

set_option maxRecDepth 4096 in
theorem native_named_inverse_checkpoint_count :
    (cRegs++cEmit++cStates++cEnd++charLocalConstraints++characterLengthConstraints++separatorConstraints++predecessorConstraints++namedInverseConstraints).length=710 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
