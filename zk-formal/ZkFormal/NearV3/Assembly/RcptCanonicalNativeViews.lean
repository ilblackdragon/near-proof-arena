import ZkFormal.NearV3.Assembly.RcptDecodedNativeSequence
import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

def DecodedEntity.view? (tr : Trace Fp) : DecodedEntity→Option RcptE
  | .header _=>none
  | .receipt y=>some (rcptOf tr 0 y)

theorem decoded_block_views (tr : Trace Fp) (bs : List ListBlock) :
    (bs.flatMap ListBlock.entities).filterMap (DecodedEntity.view? tr)=
      flatR (bs.map (RcptV3Proof.ListBlock.view tr 0)) := by
  simp only [List.filterMap_flatMap,ListBlock.entities,List.filterMap_cons,DecodedEntity.view?,
    List.filterMap_map,Function.comp_def,DecodedEntity.view?,List.filterMap_eq_map',
    flatR,List.flatMap_map,RcptV3Proof.ListBlock.view,RcptV3Proof.ListBlock.viewReceipts]

theorem native_entity_views (tr : Trace Fp) (es : List EntityPlan) (start : Nat) :
    (nativeEntities start es).filterMap (DecodedEntity.view? tr)=
      (receiptLocations start es).map (fun x=>rcptOf tr 0 (inputShape x.1 x.2.input)) := by
  induction es generalizing start with
  | nil => rfl
  | cons p ps ih =>
    cases p <;> simp only [nativeEntities,nativeEntity,List.filterMap_cons,DecodedEntity.view?,
      receiptLocations,List.map_cons,EntityPlan.rows,ih]

/-- The actual canonical ListChain's flat receipt views equal the executable
native locations. No assumed leaf identity, ordering, or layout match is used. -/
theorem canonical_native_views (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0 0 bs e) :
    flatR (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) 0))=
      locatedViews (RoutingQCandidate.patchTrace
        (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0) lists := by
  have he := decoded_native_sequence own ctx lists log constants pub digests fallback headerFallback hw hh hL
    _ e (ListChain.decoded hc) (ReceiptCandidateProof.ListChain.end_padding hc).2
  rw [←decoded_block_views,he,native_entity_views]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
