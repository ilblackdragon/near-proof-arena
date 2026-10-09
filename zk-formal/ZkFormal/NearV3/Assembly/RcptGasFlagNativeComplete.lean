import ZkFormal.NearV3.Assembly.RcptGasFlagCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_gasFlag_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++gasDelayConstraints++gasFlagConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants)))))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx (gasEffectiveAux ctx (gasDelayAux ctx (gasFlagAux ctx fallback)))))))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_gasDelay_complete hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
      accountId accessId constants pub digests (gasFlagAux ctx fallback) headerFallback hgp hprice hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_gasFlags own ctx lists hw hflags 22 pos
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k constants)))))
      pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k)
        (keyAux accountId accessId (gasEffectiveAux ctx (gasDelayAux ctx fallback))))))))))
      (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))
      hprice (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [gasEffective_constants_price,gasEffective_constants_system,gasEffective_constants_identity,
      gasEffective_constants_key,gasEffective_constants_routing,
      gasFlag_borrow_commute,gasFlag_digest_commute,gasFlag_character_commute,gasFlag_length_commute,
      gasFlag_predecessor_commute,gasFlag_named_commute,gasFlag_system_commute,
      gasFlag_routing_commute,gasFlag_key_commute,gasFlag_effective_commute,gasFlag_delay_commute,
      gasBorrow_digest_commute,gasBorrow_character_commute,gasBorrow_length_commute,
      gasBorrow_predecessor_commute,gasBorrow_named_commute,gasBorrow_system_commute,
      gasBorrow_routing_commute,gasBorrow_key_commute] using hh

set_option maxRecDepth 4096 in
theorem native_gasFlag_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++gasDelayConstraints++gasFlagConstraints).length=828 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
