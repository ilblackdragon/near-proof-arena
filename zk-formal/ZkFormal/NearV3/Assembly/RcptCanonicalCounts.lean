import ZkFormal.NearV3.Assembly.RcptCanonicalNativeEncoding
import ZkFormal.NearV3.Assembly.RcptCanonicalGroupedEncoding
import ZkFormal.NearV3.Assembly.RcptNativeCapacity

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
theorem canonical_native_counts (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable
      (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    bs.length=lists.length ∧
      (flatR (bs.map (ListBlock.view
        (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0))).length=lists.flatten.length := by
  have hg := congrArg List.length (canonical_grouped_encodings own ctx lists log constants pub digests
    fallback headerFallback hw hh hL bs e hc)
  have he := congrArg List.length (canonical_native_encodings own ctx lists log constants pub digests
    fallback headerFallback hw hh hL bs e hc)
  simp only [List.length_map] at hg he
  exact ⟨hg,he⟩

include hw in
theorem canonical_native_count_bounds {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) (hsource : lists.length=p.lists.length)
    {t : PTrie} {out : MainOut}
    (hrun : applyNewChunk prims ctx t (lists.flatten.map Input.receipt)=.ok out)
    (hgas : ctx.gasLimit≤maxGasLimitD0) (hh : 2^log<Algebra.P)
    (hL : TableLocal ReceiptCandidateRouting.candidateTable
      (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    (bs.map (ListBlock.view (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0)).length≤1984 ∧
      (flatR (bs.map (ListBlock.view
        (nativeTrace own ctx lists log constants pub digests fallback headerFallback) 0))).length≤4481 := by
  have he := canonical_native_counts own ctx lists log constants pub digests fallback headerFallback hw hh hL bs e hc
  have hs := Rcpt.Candidates.prepD0_source_count hp
  have hn := applyNewChunk_receipt_bound hrun hgas
  simp only [List.length_map] at hn ⊢
  rw [he.1,hsource,he.2]
  exact ⟨hs,hn⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
