import ZkFormal.NearV3.Assembly.RcptKeyHeaderCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_key_complete {cb bs : Bytes} {hint : Hint} {p : Prep} {k : WalkD0} {w : StateWitness}
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
    (hpub : FinalPublicBytes lists out pub)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants (keyConstants accountId (nativeRoutingConstants k constants))))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) (keyAux accountId accessId fallback)))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux (keyHeaderAux headerFallback)))))) 0 pos pub=0 := by
  obtain ⟨hv,hu⟩ := native_routing_plan hp hk hd lists hls
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_routing_complete hp own ctx lists hsource (nativeRoutingInterval k)
      hv hu hw hne hn hflags hrun hgas (keyConstants accountId (nativeRoutingConstants k constants)) pub digests
      (keyAux accountId accessId fallback) (keyHeaderAux headerFallback) hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_key own ctx lists hw 22 pos accountId accessId
      (nativeRoutingConstants k constants) pub digests
      (digestMetadata (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux (nativeRoutingInterval k) fallback))))))
      (digestHeaderMetadata (systemHeaderAux (routingHeaderAux headerFallback)))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) e he
    simpa only [key_digest_commute,key_length_commute,key_predecessor_commute,key_named_commute,
      key_system_commute,key_routing_commute,character_digest_commute,key_header_digest_commute,
      key_header_system_commute,key_header_routing_commute,character_digest_header_commute] using hh

set_option maxRecDepth 4096 in
theorem native_key_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute++cKey).length=802 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
