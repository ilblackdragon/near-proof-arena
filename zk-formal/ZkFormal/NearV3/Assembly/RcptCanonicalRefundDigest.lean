import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptNativeRid

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Every canonical refund digest hashes its actual emitted RID preimage,
including the authenticated native block-height bytes. -/
theorem canonical_refund_digests (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hheight : HeightPublicBytes ctx pub)
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
      x.hr=true→x.rfid=(sha256 ((x.rid++pubBytes pub PH_HEIGHT 8++List.replicate 8 0).map UInt8.ofNat)).map UInt8.toNat := by
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
  apply native_refund_digest own ctx lists log constants pub digests
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback a.2 pre post hb
  · have hn := hw xs hxs a.2.input hi
    simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at hn
    grind only
  · exact hheight

end ZkFormal.NearV3.Assembly.RcptSkeleton
