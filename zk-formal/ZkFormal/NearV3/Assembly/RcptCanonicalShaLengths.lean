import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptNativePeo
import ZkFormal.NearV3.Assembly.RcptNativeEncoding
import ZkFormal.NearV3.Assembly.RcptNativeShaLengths

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Native serialization bounds on the SAME canonical extracted physical views. -/
theorem canonical_native_sha_lengths (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflag : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0 0 bs e) :
    ∀x∈flatR (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0) 0)),
      x.enc.length≤347 ∧ x.peo.length≤133 ∧ x.leaf.length=68 ∧ x.rid.length=32 := by
  rw [canonical_native_views own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback hw hh
    (ReceiptCandidateProof.repaired_local_base hL) bs e hc]
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  obtain ⟨pre,post,hb,ho⟩ := native_locations_block lists a.1 a.2 ha
  have hi : a.2.input∈lists.flatten := by
    rw [←entityPlans_inputs,←receiptLocations_inputs (entityPlans lists) 0]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨xs,hxs,hi⟩ := List.mem_flatten.mp hi
  rw [ho]
  have hw' := hw xs hxs a.2.input hi
  have he := native_receipt_encoding own ctx lists log constants pub (nativeDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback a.2 pre post hb hw'
  have hp := native_peo_slice own ctx k lists accountId accessId log constants pub digests fallback
    headerFallback a.2 pre post hb hw' (hflag xs hxs a.2.input hi)
  refine ⟨?_,?_,?_,?_⟩
  · rw [he,List.length_map]
    exact native_receipt_encoded_bound _ hw'
  · rw [hp,List.length_map]
    exact native_peo_length_bound ctx _ hw'
  · simp [rcptOf,RcptV.leaf,colAt,u32r]
  · simp [rcptOf,colAt]

end ZkFormal.NearV3.Assembly.RcptSkeleton
