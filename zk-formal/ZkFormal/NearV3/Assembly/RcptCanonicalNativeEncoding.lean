import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptNativeEncoding

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)

private abbrev nativeTrace := RoutingQCandidate.patchTrace
  (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0

include hw in
theorem located_native_encodings :
    (locatedViews (nativeTrace own ctx lists log constants pub digests fallback headerFallback) lists).map
      (fun x=>x.enc)=lists.flatten.map (fun x=>x.receipt.encode.map UInt8.toNat) := by
  have hi := receiptLocations_inputs (entityPlans lists) 0
  rw [entityPlans_inputs] at hi
  rw [←hi,List.map_map]
  unfold locatedViews
  rw [List.map_map]
  apply List.map_congr_left
  intro a ha
  obtain ⟨pre,post,hb,ho⟩ := native_locations_block lists a.1 a.2 ha
  have hm : a.2.input∈lists.flatten := by rw [←hi];exact List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨xs,hxs,hm⟩ := List.mem_flatten.mp hm
  dsimp only [Function.comp_def]
  rw [ho]
  exact native_receipt_encoding own ctx lists log constants pub digests fallback headerFallback
    a.2 pre post hb (hw xs hxs a.2.input hm)

include hw in
theorem canonical_native_encodings (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable
      (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    (flatR (bs.map (RcptV3Proof.ListBlock.view
      (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0))).map (fun x=>x.enc)=
      lists.flatten.map (fun x=>x.receipt.encode.map UInt8.toNat) := by
  rw [canonical_native_views own ctx lists log constants pub digests fallback headerFallback hw hh
    (ReceiptCandidateProof.repaired_local_base hL) bs e hc]
  exact located_native_encodings own ctx lists log constants pub digests fallback headerFallback hw

end ZkFormal.NearV3.Assembly.RcptSkeleton
