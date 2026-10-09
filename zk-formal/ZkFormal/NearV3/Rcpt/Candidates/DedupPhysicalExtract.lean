import ZkFormal.NearV3.Rcpt.Candidates.DedupJoinedTraffic
import ZkFormal.NearV3.Rcpt.Candidates.DedupSourceReuse

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- The two physical source partitions extract one semantic sequence with exact
external multiplicities. Only the isolated continuation-bus balance is assumed;
no honest renderer, reconstructed witness, or old log20 source cap is assumed. -/
theorem physical_source_extract {tr : Trace Fp} {left right : Nat} {pub : List Fp}
    (hleft : TableLocal (leftTable sourceCarryBus) tr left pub)
    (hright : TableLocal (rightTable sourceCarryBus) tr right pub)
    (hheight : tr.height right=tr.height left)
    (hbal : ∀ m,
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus true m+
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus true m=
      tableBusCount (leftInteractions sourceCarryBus) tr left pub sourceCarryBus false m+
      tableBusCount (rightInteractions sourceCarryBus) tr right pub sourceCarryBus false m) :
    ∃ bs stop,
      TableLocal (DedupTable.table 24) (joinedTrace tr left right) 0 pub ∧
      DedupProof.BlockChain (joinedTrace tr left right) 0 0 bs stop ∧
      bs≠[] ∧ DedupRender.R bs≤2*tr.height left ∧
      ∀ bus, bus≠sourceCarryBus → ∀ sd m,
        tableBusCount (leftInteractions sourceCarryBus) tr left pub bus sd m+
        tableBusCount (rightInteractions sourceCarryBus) tr right pub bus sd m=
        cnt (DedupProof.sourceMsgs (joinedTrace tr left right) 0 bs bus sd) m := by
  obtain ⟨hL, hc⟩ := joined_sound hleft hright hheight hbal
  obtain ⟨bs, stop, hb⟩ := DedupProof.extract_blocks hL
  refine ⟨bs, stop, hL, hb, hb.nonempty, ?_, ?_⟩
  · have hrows := hb.rows
    have hbound := hb.bound
    rw [joined_height] at hbound
    omega
  · intro bus hbus sd m
    rw [← hc bus hbus sd m, tableBusCount_eq, hb.all_traffic hL bus sd]
    rfl

end ZkFormal.NearV3.Rcpt.Candidates.DedupPartitionTable
