import ZkFormal.NearV3.Assembly.RcptSystemTrafficPhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched

theorem booleanReceiptTrace_native_systemBalance {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hsource : lists.length=p.lists.length)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    let tr := booleanReceiptTrace own ctx lists 22
      (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests
      (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux (systemAux fallback))))))
      (digestHeaderMetadata (characterHeaderAux (systemHeaderAux headerFallback)))
    (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC true)=
      (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC false) := by
  have hh := booleanReceiptTrace_systemBalance own ctx lists 22
    (nativePriceConstants ctx (systemConstants (systemIdentityConstants constants))) pub digests
    (digestMetadata (characterAux (characterLengthAux (predecessorAux (namedAux fallback)))))
    (digestHeaderMetadata (characterHeaderAux headerFallback))
    (Nat.le_of_lt (native_plannedRows_capacity hp lists hsource hw hrun hgas).2)
  simpa only [system_digest_commute,system_character_commute,system_length_commute,
    system_predecessor_commute,system_named_commute,system_header_digest_commute,system_header_character_commute] using hh

end ZkFormal.NearV3.Assembly.RcptSkeleton
