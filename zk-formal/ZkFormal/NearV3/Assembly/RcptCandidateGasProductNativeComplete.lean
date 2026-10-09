import ZkFormal.NearV3.Assembly.RcptCandidateGasTokenNativeComplete

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_candidateGasProduct_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++candidateGasDelayConstraints++gasFlagConstraints++gasAccumulatorConstraints++gasProductConstraints systemSurplus,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants)))))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx (gasEffectiveAux ctx (candidateGasDelayAux ctx (gasFlagAux ctx (gasTokenAux (receiptPlanToken ctx lists) (gasProductAux ctx fallback)))))))))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_candidateGasToken_complete hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
      accountId accessId constants pub digests (gasProductAux ctx fallback) headerFallback hgp hprice hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_acceptedGasProduct own ctx lists hw hrun hprice 22 pos
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k constants)))))
      pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux
        (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasFlagAux ctx fallback)))))))))
      (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [nativeGasProductAux,
      gasEffective_constants_price,gasEffective_constants_system,gasEffective_constants_identity,
      gasEffective_constants_key,gasEffective_constants_routing,
      gasToken_digest_commute,gasToken_character_commute,gasToken_length_commute,
      gasToken_predecessor_commute,gasToken_named_commute,gasToken_system_commute,
      gasToken_routing_commute,gasToken_key_commute,gasToken_flag_commute,
      gasBorrow_digest_commute,gasBorrow_character_commute,gasBorrow_length_commute,
      gasBorrow_predecessor_commute,gasBorrow_named_commute,gasBorrow_system_commute,
      gasBorrow_routing_commute,gasBorrow_key_commute,
      gasEffective_digest_commute,gasEffective_character_commute,gasEffective_length_commute,
      gasEffective_predecessor_commute,gasEffective_named_commute,gasEffective_system_commute,
      gasEffective_routing_commute,gasEffective_key_commute,gasEffective_borrow_commute,
      candidateGasDelay_digest_commute,candidateGasDelay_character_commute,candidateGasDelay_length_commute,
      candidateGasDelay_predecessor_commute,candidateGasDelay_named_commute,candidateGasDelay_system_commute,
      candidateGasDelay_routing_commute,candidateGasDelay_key_commute,
      ←gasBorrow_candidateDelay_commute,←gasEffective_candidateDelay_commute,
      gasProduct_digest_commute,gasProduct_character_commute,gasProduct_length_commute,
      gasProduct_predecessor_commute,gasProduct_named_commute,gasProduct_system_commute,
      gasProduct_routing_commute,gasProduct_key_commute,
      ←gasBorrow_product_commute,←gasEffective_product_commute,←candidateGasDelay_product_commute,
      ←gasFlag_product_commute,←gasToken_product_commute] using hh

set_option maxRecDepth 4096 in
theorem native_candidateGasProduct_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++gasBorrowConstraints++gasEffectiveConstraints++candidateGasDelayConstraints++gasFlagConstraints++gasAccumulatorConstraints++gasProductConstraints systemSurplus).length=842 := by decide

theorem systemGasConstraints_split : systemGasConstraints=
    gasBorrowConstraints++gasEffectiveConstraints++gasProductConstraints systemSurplus++
      gasAccumulatorConstraints++gasFlagConstraints++candidateGasDelayConstraints := rfl

theorem booleanReceiptTrace_native_candidateGas_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey++systemGasConstraints,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k (gasEffectiveConstants ctx constants)))))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId (gasBorrowAux ctx (gasEffectiveAux ctx (candidateGasDelayAux ctx (gasFlagAux ctx (gasTokenAux (receiptPlanToken ctx lists) (gasProductAux ctx fallback)))))))))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))) 0 pos pub=0 := by
  intro pos hpos e he
  apply booleanReceiptTrace_native_candidateGasProduct_complete hp hk hd own ctx lists hsource hls hw hne hn hflags hrun hgas
    accountId accessId constants pub digests fallback headerFallback hgp hprice hpub hown pos hpos e
  simp only [systemGasConstraints_split,List.mem_append] at he ⊢
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
