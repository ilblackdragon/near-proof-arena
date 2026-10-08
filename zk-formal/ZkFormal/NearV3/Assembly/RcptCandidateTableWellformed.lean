import ZkFormal.NearV3.Assembly.RcptCandidateReceiptCanon
-- Source TableWellformed.lean SHA256: 09fc3f9e94fdea3a8d0ebe38009beb18bf0b9a91cb4de5e57f1da68cd91ec421.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.NaturalTotals
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptCanon

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Semantic flattened count is the sum of physical list receipt counts. -/
theorem flat_views_length (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    (flatR (bs.map (ListBlock.view tr tt))).length=(bs.map fun B => B.receipts.length).sum := by
  rw [flat_views,List.length_map]
  induction bs with
  | nil => simp
  | cons B bs ih => simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,ih]

/-- Semantic refund-body endpoint is the total already extracted from physical rows. -/
theorem flat_views_body (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    bOffs (flatR (bs.map (ListBlock.view tr tt))) (flatR (bs.map (ListBlock.view tr tt))).length=
      8+(bs.map fun B => B.refundBytes tr tt).sum := by
  simp only [bOffs,List.take_length,flat_views,List.map_map,Function.comp_def,List.map_flatMap]
  congr 1
  induction bs with
  | nil => simp
  | cons B bs ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]
    rfl

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- Complete extracted receipt wellformedness, correctly scoped to admissible
public totals. The actual previous-version provider bound remains explicit. -/
theorem ListChain.view_wf {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hprovider : ∀ B∈bs, ∀ y∈B.receipts, (rcptOf tr tt y).tprev≤2^22) : RcptV3Wf pub (bs.map (ListBlock.view tr tt)) := by
  refine ⟨(ListChain.view_header_facts hL h).1,ListChain.view_tokens hL h hprovider,?_,(ListChain.view_header_facts hL h).2.1,?_,ListChain.view_canon hL h⟩
  · intro hb
    rw [flat_views_length]
    exact ListChain.natural_count hL h hp.count hb
  · intro hb
    rw [flat_views_body]
    exact ListChain.natural_body hL h hp.body hb

/-- Actual receipt AIR admits wellformed semantic lists when the packed public
totals are admissible. Traffic equality remains a separate extraction obligation. -/
theorem extract_wellformed (hp : ReceiptPublicRanges pub)
    (hprovider : ∀ y : RS, Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt →
      (rcptOf tr tt y).tprev≤2^22) :
    ∃ ls,RcptV3Wf pub ls := by
  obtain ⟨bs,e,hc⟩ := extract_lists hL
  exact ⟨bs.map (ListBlock.view tr tt),ListChain.view_wf hL hc hp (fun B hB y hy=>hprovider y ((hc.blocks B hB).layouts y hy))⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
