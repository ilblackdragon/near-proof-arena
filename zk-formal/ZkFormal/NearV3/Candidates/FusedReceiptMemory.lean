import ZkFormal.NearV3.Candidates.FusedReceiptTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateMemoryVersion
namespace ZkFormal.NearV3.Candidates.FusedReceiptMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace
open Assembly.ReceiptCandidateRouting RcptV3Proof

private theorem mem_le_sum {n : Nat} {xs : List Nat} (h : n∈xs) : n≤xs.sum := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp
    · have := ih h; simp only [List.sum_cons];omega

/-- A physical fused MEM receive bound suffices for the projected receipt
semantics. The global provider/ownership proof must supply this stream bound. -/
theorem extract_sound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal (fuse GatedMemoryFusion.selected) tr t pub)
    (hp : Assembly.ReceiptCandidateProof.ReceiptPublicRanges pub)
    (hm : ∀msg : List Fp,
      0<tableBusCount (fuse GatedMemoryFusion.selected).interactions tr t pub B_MEM false msg→
      (msg.getD 1 0).toNat≤2^22) :
    ∃off,∃bs : List ListBlock,∃e,
      ListChain (project off tr) t 0 bs e ∧
      RcptV3Wf pub (bs.map (ListBlock.view (project off tr) t)) ∧
      TableTraffic candidateTable.interactions (project off tr) t pub
        (rcptTraffic3 pub (bs.map (ListBlock.view (project off tr) t))) := by
  have hmem:=FusedReceiptTraffic.receipt_member
  rw [←HorizontalProjection.split_tables GatedMemoryFusion.selected tr 0] at hmem
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hmem
  obtain ⟨off,hloc,hproject⟩:=HorizontalProjection.split_location _ _ _ hx
  rw [he] at hloc
  have hl:=project_local hloc (show candidateTable.maxLog=22 by rfl) h
  obtain ⟨bs,e,hc,_⟩:=Assembly.ReceiptCandidateProof.repaired_extract_traffic hl
  refine ⟨off,bs,e,hc,?_⟩
  apply Assembly.ReceiptCandidateProof.repaired_sound_of_mem_stream hl hc hp
  intro msg hpos
  apply hm msg
  rw [HorizontalProjection.fused_count]
  have hle:=mem_le_sum (List.mem_map.mpr ⟨x,hx,rfl⟩ :
    tableBusCount x.1.interactions x.2 t pub B_MEM false msg∈
    ((HorizontalProjection.split tr 0 GatedMemoryFusion.selected).map
      (fun z=>tableBusCount z.1.interactions z.2 t pub B_MEM false msg)))
  rw [he,hproject] at hle
  omega
end ZkFormal.NearV3.Candidates.FusedReceiptMemory
