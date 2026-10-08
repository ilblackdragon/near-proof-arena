import ZkFormal.NearV3.Assembly.RcptGasDelayCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_gasDelay_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
    (hp : prepD0 cb hint=.ok p) (hk : walkD0 cb=.ok k) (hd : decodeStateWitness bs=.ok w) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hls : lists.flatten.map Input.receipt=appliedReceipts k w)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hne : lists≠[])
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (hflags : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hgp : GasPublicBytes ctx pub) (hprice : ctx.gasPrice<256^16)
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++gasDelayConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants)))))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx (gasEffectiveAux ctx (gasDelayAux ctx fallback))))))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_gasEffective_complete hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
      accountId accessId constants pub digests (gasDelayAux ctx fallback) headerFallback hgp hprice hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_gasDelay own ctx lists 22 pos
      (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants))))) pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId fallback))))))))
      (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [gasEffective_borrow_commute,←gasBorrow_delay_commute,←gasEffective_delay_commute,
      gasBorrow_digest_commute,gasBorrow_character_commute,gasBorrow_length_commute,
      gasBorrow_predecessor_commute,gasBorrow_named_commute,gasBorrow_system_commute,
      gasBorrow_routing_commute,gasBorrow_key_commute,
      gasEffective_digest_commute,gasEffective_character_commute,gasEffective_length_commute,
      gasEffective_predecessor_commute,gasEffective_named_commute,gasEffective_system_commute,
      gasEffective_routing_commute,gasEffective_key_commute,
      gasDelay_digest_commute,gasDelay_character_commute,gasDelay_length_commute,
      gasDelay_predecessor_commute,gasDelay_named_commute,gasDelay_system_commute,
      gasDelay_routing_commute,gasDelay_key_commute] using hh

set_option maxRecDepth 4096 in
theorem native_gasDelay_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++gasDelayConstraints).length=824 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
