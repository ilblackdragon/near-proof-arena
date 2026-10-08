import ZkFormal.NearV3.Assembly.RcptCandidateTableTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateBounds

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof

/-- Every interaction of the fully repaired receipt table is accounted for by
its actual extracted list views. No public ranges or old TableLocal are assumed. -/
theorem repaired_view_traffic {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e) :
    TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
      (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  exact ListChain.view_traffic (repaired_local_base hL) hc

/-- The same physical list chain witnesses complete repaired-table traffic. -/
theorem repaired_extract_traffic {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub) :
    ∃ bs e, ListChain tr tt 0 bs e ∧
      TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
        (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  obtain ⟨bs,e,hc⟩ := extract_lists (repaired_local_base hL)
  exact ⟨bs,e,hc,repaired_view_traffic hL hc⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
