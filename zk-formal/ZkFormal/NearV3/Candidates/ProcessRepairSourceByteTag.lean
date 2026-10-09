import ZkFormal.NearV3.Candidates.ProcessRepairSourceView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceByteTag
import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableSound
import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableMessages
import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractCounters
namespace ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open Rcpt.Candidates ProcPriorRoutedSourceView
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

open ProcPriorRoutedSourceByteTag (logical logical_tag)

theorem local_logical {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66) :
    TableLocal (DedupTable.table 24) (logical tr) 0 pub := by
  obtain ⟨h01,h12,h23⟩:=ProcessRepairSourceView.cells v hpub
  exact SourceLog22.variable_local (ProcessRepairSourceView.local_source 0 (by decide) v)
    (ProcessRepairSourceView.local_source 1 (by decide) v) (ProcessRepairSourceView.local_source 2 (by decide) v)
    (ProcessRepairSourceView.local_source 3 (by decide) v) h01 h12 h23

theorem bytes_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (v:ProcessRepairInterface.View AP pub tr) (msg:List Fp) :
    SourceLog22.boundaryCount (source tr) 0 1 2 3 pub B_BYTES true msg=
      tableBusCount DedupTable.interactions (logical tr) 0 pub B_BYTES true msg := by
  have h:=SourceLog22.counted_variable_external_counts (ProcessRepairSourceView.local_source 0 (by decide) v)
    (ProcessRepairSourceView.local_source 1 (by decide) v) (ProcessRepairSourceView.local_source 2 (by decide) v)
    (ProcessRepairSourceView.local_source 3 (by decide) v) B_BYTES true (by decide) (by decide) (by decide) msg
  rw [show (SizeCount.sourceTable (DedupTable.table 24)).interactions=
    (DedupTable.table 24).interactions.map (SizeCount.withCount (ZkFormal.Near.Dsl.k 0)) from rfl] at h
  rw [SizeCount.count_nonSize _ _ B_BYTES (by decide)] at h
  exact h

/-- Actual source-partition byte providers have tag13. Their counters and all
three cross-partition joins follow from the installed AIR and real bus balance. -/
theorem tag {AP:AirP} {tr:Trace Fp} {pub msg:List Fp}
    (v:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (j:Nat) (hj:j<4)
    (hm:tableBusCount (base j).interactions (source tr) j pub B_BYTES true msg≠0) :
    msg[0]!.toNat%16=13 := by
  apply logical_tag (local_logical v hpub)
  rw [←bytes_count v]
  unfold SourceLog22.boundaryCount
  have hcases:j=0 ∨ j=1 ∨ j=2 ∨ j=3:=by omega
  rcases hcases with rfl|rfl|rfl|rfl
  · change tableBusCount (SizeCount.sourceTable SourceLog22.firstTable).interactions (source tr) 0 pub B_BYTES true msg≠0 at hm
    omega
  · change tableBusCount (SizeCount.sourceTable (SourceLog22.middleTable 64 65)).interactions (source tr) 1 pub B_BYTES true msg≠0 at hm
    omega
  · change tableBusCount (SizeCount.sourceTable (SourceLog22.middleTable 65 66)).interactions (source tr) 2 pub B_BYTES true msg≠0 at hm
    omega
  · change tableBusCount (SizeCount.sourceTable SourceLog22.lastTable).interactions (source tr) 3 pub B_BYTES true msg≠0 at hm
    omega
end ZkFormal.NearV3.Candidates.ProcessRepairSourceByteTag
