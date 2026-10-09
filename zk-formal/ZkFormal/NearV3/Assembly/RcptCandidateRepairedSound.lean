import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateTableWellformed

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3Proof

/-- The fully repaired table yields semantic wellformedness and all-bus traffic
for exactly the same physical lists. Memory-version ownership remains explicit. -/
theorem repaired_view_sound {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hprovider : ∀ B∈bs, ∀ y∈B.receipts, (rcptOf tr tt y).tprev≤2^22) :
    RcptV3Wf pub (bs.map (ListBlock.view tr tt)) ∧
      TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
        (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) :=
  ⟨ListChain.view_wf (repaired_local_base hL) hc hp hprovider,
    repaired_view_traffic hL hc⟩

/-- A flattened-view provider bound suffices; the caller need not reason about
internal list blocks or receipt-layout offsets. -/
theorem repaired_view_sound_of_flat {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal ReceiptCandidateRouting.candidateTable tr tt pub)
    {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hprovider : ∀ x∈flatR (bs.map (ListBlock.view tr tt)), x.tprev≤2^22) :
    RcptV3Wf pub (bs.map (ListBlock.view tr tt)) ∧
      TableTraffic ReceiptCandidateRouting.candidateTable.interactions tr tt pub
        (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  apply repaired_view_sound hL hc hp
  intro B hB y hy
  apply hprovider (rcptOf tr tt y)
  rw [flat_views]
  exact List.mem_map.mpr ⟨y,List.mem_flatMap.mpr ⟨B,hB,hy⟩,rfl⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
