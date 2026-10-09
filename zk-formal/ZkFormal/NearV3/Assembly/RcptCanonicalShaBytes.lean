import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews
import ZkFormal.NearV3.Assembly.RcptNativePeo
import ZkFormal.NearV3.Assembly.RcptNativeEncoding
import ZkFormal.NearV3.Assembly.RcptNativeShaLengths
import ZkFormal.NearV3.Assembly.RcptNativeRid

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Native serialization bounds on the SAME canonical extracted physical views. -/
theorem canonical_native_sha_bytes (own : Nat) (ctx : ApplyCtx) (k : WalkD0) (lists : List (List Input))
    (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hflag : ∀xs∈lists,∀x∈xs,x.refund=nativeRefund ctx x.receipt)
    (hheight : HeightPublicBytes ctx pub) (hh : 2^log<Algebra.P)
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
      ∀bytes∈Rcpt.Candidates.receiptShaPayloads pub x,∀b∈bytes,b<256 := by
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
  have hid : a.2.input.receipt.receiptId.length=32 := by
    simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at hw'
    grind only
  have hp := native_peo_slice own ctx k lists accountId accessId log constants pub digests fallback
    headerFallback a.2 pre post hb hw' (hflag xs hxs a.2.input hi)
  have hl := native_leaf own ctx lists log constants pub (refundDigests ctx digests)
    (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback a.2 pre post hb hid
  have hrid : (rcptOf (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (nativeDigests ctx digests)
        (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback) 0)
      0 (inputShape pre.length a.2.input)).rid=a.2.input.receipt.receiptId.map UInt8.toNat := by
    change colAt (RoutingQCandidate.patchTrace _ 0) 0 _ 32 RcptV3.b=_
    rw [patch_byte_slice]
    exact native_rid_slice own ctx lists log constants pub (nativeDigests ctx digests)
      (completeReceiptAux ctx k lists accountId accessId fallback) headerFallback a.2 pre post hb hid
  intro bytes hbytes b hbyte
  simp only [Rcpt.Candidates.receiptShaPayloads,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hbytes
  rcases hbytes with (rfl|rfl)|hrefund
  · rw [hp] at hbyte
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hbyte
    exact UInt8.toNat_lt v
  · simp only [nativeDigests] at hbyte
    rw [hl] at hbyte
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hbyte
    exact UInt8.toNat_lt v
  · split at hrefund
    · simp only [List.mem_singleton] at hrefund
      subst bytes
      rw [hrid,native_height_bytes ctx pub hheight] at hbyte
      simp only [List.mem_append,List.mem_replicate] at hbyte
      rcases hbyte with (hbyte|hbyte)|⟨_,rfl⟩
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hbyte; exact UInt8.toNat_lt v
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hbyte; exact UInt8.toNat_lt v
      · decide
    · contradiction

end ZkFormal.NearV3.Assembly.RcptSkeleton
