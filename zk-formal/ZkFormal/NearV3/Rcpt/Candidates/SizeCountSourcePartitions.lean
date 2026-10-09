import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourceSender
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountValComplete
import ZkFormal.NearV3.Rcpt.Candidates.DedupPhysicalExtract

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open DedupPartitionTable

theorem source_local_base {T : ZkFormal.Air.Table} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal (sourceTable T) tr t pub) : TableLocal T tr t pub := by
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  have hm : b∈(withCount (k 0) i).mult := by unfold withCount; split <;> exact hb
  exact h.bits r hr _ (List.mem_map.mpr ⟨i,hi,rfl⟩) b hm

/-- Both accepting physical partitions supply exactly ONE source SIZE record for
the same extracted BlockChain. The carry bus is unchanged by the arity extension. -/
theorem partition_size_sender {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hl : TableLocal (sourceTable (leftTable sourceCarryBus)) tr left pub)
    (hr : TableLocal (sourceTable (rightTable sourceCarryBus)) tr right pub)
    (hh : tr.height right=tr.height left)
    (hbal : ∀ m,
      tableBusCount (sourceTable (leftTable sourceCarryBus)).interactions tr left pub sourceCarryBus true m+
      tableBusCount (sourceTable (rightTable sourceCarryBus)).interactions tr right pub sourceCarryBus true m=
      tableBusCount (sourceTable (leftTable sourceCarryBus)).interactions tr left pub sourceCarryBus false m+
      tableBusCount (sourceTable (rightTable sourceCarryBus)).interactions tr right pub sourceCarryBus false m) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (joinedTrace tr left right) 0 pub ∧
      DedupProof.BlockChain (joinedTrace tr left right) 0 0 bs stop ∧
      ((List.range (tr.height left)).flatMap (fun r =>
        rowTraffic (sourceTable (leftTable sourceCarryBus)).interactions tr left r pub B_SIZE true))++
      ((List.range (tr.height right)).flatMap (fun r =>
        rowTraffic (sourceTable (rightTable sourceCarryBus)).interactions tr right r pub B_SIZE true))=
      [[2,(((bs.map fun B => B.L+33*B.path.length).sum:Nat):Fp),0]] := by
  have hl0 := source_local_base hl
  have hr0 := source_local_base hr
  have hb0 : ∀ m,
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m+
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m=
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m+
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m := by
    intro m
    have hb := hbal m
    simp only [sourceTable] at hb
    simp only [count_nonSize _ _ sourceCarryBus (by decide)] at hb
    exact hb
  obtain ⟨hjoined,_⟩ := joined_sound hl0 hr0 hh hb0
  obtain ⟨bs,stop,hbs⟩ := DedupProof.extract_blocks hjoined
  refine ⟨bs,stop,hjoined,hbs,?_⟩
  rw [source_size_traffic,source_size_traffic,←List.map_append]
  have hj := joined_messages hr0 hh B_SIZE true (by decide)
  simp only [leftTable,rightTable]
  rw [←hj,hbs.all_traffic hjoined]
  simp [DedupProof.sourceMsgs,Msg.toFp]
  exact ⟨rfl,rfl⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
