import ZkFormal.NearV3.Assembly.RcptRoutingHeaderCommute

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched RoutingBoundedLayout

theorem booleanReceiptTrace_native_routing_complete {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (interval : ReceiptPlan→Option Bytes×Option Bytes)
    (hv : ∀rp,rp.input∈lists.flatten→inInterval rp.input.receipt.receiverId (interval rp)=true)
    (hu : ∀rp,rp.input∈lists.flatten→∀v∈(interval rp).2.getD [],0<v.toNat)
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
    ∀pos,pos<2^22→∀e∈cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute,
      e.eval (booleanReceiptTrace own ctx lists 22 (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux (routingAux interval fallback))))))) (digestHeaderMetadata (characterHeaderAux (systemHeaderAux (routingHeaderAux headerFallback))))) 0 pos pub=0 := by
  intro pos hpos e he
  rcases List.mem_append.mp he with he|he
  · exact booleanReceiptTrace_native_system_complete hp own ctx lists hsource hw hne hn hflags hrun hgas
      constants pub digests (routingAux interval fallback) (routingHeaderAux headerFallback) hpub hown pos hpos e he
  · have hh := booleanReceiptTrace_route own ctx lists hw 22 pos
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests interval
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux fallback))))))
      (digestHeaderMetadata (characterHeaderAux (systemHeaderAux headerFallback)))
      (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2) hv hu e he
    simpa only [routing_digest_commute,routing_character_commute,routing_length_commute,
      routing_predecessor_commute,routing_named_commute,routing_system_commute,
      routing_header_digest_commute,routing_header_character_commute,routing_header_system_commute] using hh

set_option maxRecDepth 4096 in
theorem native_routing_complete_count :
    (cRegs++cEmit++cStates++cEnd++cChars++cSys++cRoute).length=753 := by decide

end ZkFormal.NearV3.Assembly.RcptSkeleton
