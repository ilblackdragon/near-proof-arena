import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Leaf identity for the SAME canonical views extracted from the repaired
honest physical receipt trace, bound to actual successful native execution. -/
theorem canonical_executed_leaves (prims : Prims) (own : Nat) (ctx : ApplyCtx) (t : PTrie)
    (lists : List (List Input)) (out : MainOut)
    (hex : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests) fallback headerFallback) 0) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests) fallback headerFallback) 0) 0 0 bs e) :
    (flatR (bs.map (RcptV3Proof.ListBlock.view (RoutingQCandidate.patchTrace
      (booleanReceiptTrace own ctx lists log constants pub (outcomeDigests ctx digests) fallback headerFallback) 0) 0))).map
      (fun x=>x.leaf)=out.outcomes.map (fun o=>(u32 2++o.id++sha256 o.partialEncode).map UInt8.toNat) := by
  rw [canonical_native_views own ctx lists log constants pub (outcomeDigests ctx digests) fallback headerFallback
    hw hh (ReceiptCandidateProof.repaired_local_base hL) bs e hc]
  apply executed_leaves prims own ctx t lists out hex log constants pub digests fallback headerFallback
  intro x hx
  obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx
  have h := hw xs hxs x hx
  simp only [Receipt.wf,Bool.and_eq_true,beq_iff_eq] at h
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
