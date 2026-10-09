import ZkFormal.NearV3.Candidates.GatedMemoryFusion
import ZkFormal.NearV3.Candidates.HorizontalProjection
import ZkFormal.NearV3.Assembly.RcptCandidateRepairedSound

namespace ZkFormal.NearV3.Candidates.FusedReceiptTraffic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace
open Assembly.ReceiptCandidateRouting RcptV3Proof

 theorem receipt_member : candidateTable∈GatedMemoryFusion.selected := by
  apply List.mem_append_left
  exact List.mem_of_getElem? (show HorizontalReceipt.selected[13]?=some candidateTable by rfl)

/-- Receipt extraction from the actual fused column block, including equality
of every shifted physical bus count. No separate receipt witness is assumed.
This is a component extraction result, not full global AIR soundness. -/
theorem extract {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal (fuse GatedMemoryFusion.selected) tr t pub) :
    ∃off,∃bs : List ListBlock,∃e,
      TableLocal candidateTable (project off tr) t pub ∧
      ListChain (project off tr) t 0 bs e ∧
      TableTraffic candidateTable.interactions (project off tr) t pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) t))) ∧
      ∀bus sd msg,tableBusCount (shifted off candidateTable).interactions tr t pub bus sd msg=
        tableBusCount candidateTable.interactions (project off tr) t pub bus sd msg := by
  have hm:=receipt_member
  rw [←HorizontalProjection.split_tables GatedMemoryFusion.selected tr 0] at hm
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hm
  obtain ⟨off,hloc,hproject⟩:=HorizontalProjection.split_location _ _ _ hx
  rw [he] at hloc
  have hreceipt:=project_local hloc (show candidateTable.maxLog=22 by rfl) h
  obtain ⟨bs,e,hchain,htraffic⟩:=Assembly.ReceiptCandidateProof.repaired_extract_traffic hreceipt
  exact ⟨off,bs,e,hreceipt,hchain,htraffic,
    fun bus sd msg=>HorizontalProjection.shifted_count _ _ _ _ _ bus sd msg⟩
/-- Semantic receipt wellformedness uses the same extracted fused views.
Authenticated MEM ownership must still discharge the explicit version bound. -/
theorem extract_sound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal (fuse GatedMemoryFusion.selected) tr t pub)
    (hp : Assembly.ReceiptCandidateProof.ReceiptPublicRanges pub) :
    ∃off,∃bs : List ListBlock,∃e,
      TableLocal candidateTable (project off tr) t pub ∧
      ListChain (project off tr) t 0 bs e ∧
      TableTraffic candidateTable.interactions (project off tr) t pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) t))) ∧
      ((∀x∈flatR (bs.map (ListBlock.view (project off tr) t)),x.tprev≤2^22)→
        RcptV3Wf pub (bs.map (ListBlock.view (project off tr) t))) := by
  obtain ⟨off,bs,e,hl,hc,ht,_⟩:=extract h
  exact ⟨off,bs,e,hl,hc,ht,fun hb=>
    (Assembly.ReceiptCandidateProof.repaired_view_sound_of_flat hl hc hp hb).1⟩

end ZkFormal.NearV3.Candidates.FusedReceiptTraffic
