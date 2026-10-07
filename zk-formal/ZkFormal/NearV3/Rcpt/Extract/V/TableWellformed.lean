import ZkFormal.NearV3.Rcpt.Extract.V.NaturalTotals
import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptCanon

namespace ZkFormal.NearV3.RcptV3Proof
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
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Complete extracted receipt wellformedness, correctly scoped to admissible
public totals. No receipt-view semantic property is an assumed premise. -/
theorem ListChain.view_wf {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub) : RcptV3Wf pub (bs.map (ListBlock.view tr tt)) := by
  refine ⟨(h.view_header_facts hL).1,h.view_tokens hL,?_,(h.view_header_facts hL).2.1,?_,h.view_canon hL⟩
  · intro hb
    rw [flat_views_length]
    exact h.natural_count hL hp.count hb
  · intro hb
    rw [flat_views_body]
    exact h.natural_body hL hp.body hb

/-- Actual receipt AIR admits wellformed semantic lists when the packed public
totals are admissible. Traffic equality remains a separate extraction obligation. -/
theorem extract_wellformed (hp : ReceiptPublicRanges pub) :
    ∃ ls,RcptV3Wf pub ls := by
  obtain ⟨bs,e,hc⟩ := extract_lists hL
  exact ⟨bs.map (ListBlock.view tr tt),hc.view_wf hL hp⟩

end ZkFormal.NearV3.RcptV3Proof
