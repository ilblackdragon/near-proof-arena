import ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceBoundary
import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableSound
import ZkFormal.NearV3.Rcpt.Candidates.SourceVariableMessages
import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractCounters
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceByteTag
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open Rcpt.Candidates ProcPriorRoutedSourceView
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def logical (tr:Trace Fp):Trace Fp:=SourceLog22.variableTrace (source tr) 0 1 2 3

theorem local_logical {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66) :
    TableLocal (DedupTable.table 24) (logical tr) 0 pub := by
  obtain ⟨h01,h12,h23⟩:=ProcPriorRoutedSourceBoundary.cells hH htables hpub
  exact SourceLog22.variable_local (local_source 0 (by decide) hH htables)
    (local_source 1 (by decide) hH htables) (local_source 2 (by decide) hH htables)
    (local_source 3 (by decide) hH htables) h01 h12 h23

theorem bytes_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) :
    SourceLog22.boundaryCount (source tr) 0 1 2 3 pub B_BYTES true msg=
      tableBusCount DedupTable.interactions (logical tr) 0 pub B_BYTES true msg := by
  have h:=SourceLog22.counted_variable_external_counts (local_source 0 (by decide) hH htables)
    (local_source 1 (by decide) hH htables) (local_source 2 (by decide) hH htables)
    (local_source 3 (by decide) hH htables) B_BYTES true (by decide) (by decide) (by decide) msg
  rw [show (SizeCount.sourceTable (DedupTable.table 24)).interactions=
    (DedupTable.table 24).interactions.map (SizeCount.withCount (ZkFormal.Near.Dsl.k 0)) from rfl] at h
  rw [SizeCount.count_nonSize _ _ B_BYTES (by decide)] at h
  exact h

theorem logical_tag {tr:Trace Fp} {pub msg:List Fp}
    (hL:TableLocal (DedupTable.table 24) tr 0 pub)
    (hm:tableBusCount DedupTable.interactions tr 0 pub B_BYTES true msg≠0) :
    msg[0]!.toNat%16=13 := by
  obtain ⟨r,hr,i,hi,hb,hs,he,hm⟩:=exists_of_tableBusCount hm
  have hei:i=DedupTable.interactions[0]!:=by
    simp only [DedupTable.interactions,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · rfl
    all_goals contradiction
  subst i
  have hg:tr.cell 0 r SrcpV3.sg=1:=by
    by_cases hg:tr.cell 0 r SrcpV3.sg=1
    · exact hg
    · change (if tr.cell 0 r SrcpV3.sg=1 then 1 else 0)+0≠0 at hm
      simp [hg] at hm
  have hid:=DedupProof.counter_id_lt hL hr (Or.inr hg)
  rw [←he]
  change (Fp.ofNat 13+Fp.ofNat 16*tr.cell 0 r SrcpV3.q).toNat%16=13
  rw [←Fp.ofNat_toNat (tr.cell 0 r SrcpV3.q),ofNat_mul',ofNat_add',Fp.toNat_ofNat]
  change 13+16*(tr.cell 0 r SrcpV3.q).toNat<P at hid
  rw [Nat.mod_eq_of_lt hid]
  omega

/-- Actual source-partition byte providers have tag13. Their counters and all
three cross-partition joins follow from the installed AIR and real bus balance. -/
theorem tag {AP:AirP} {tr:Trace Fp} {pub msg:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠64 ∧ seg.bus≠65 ∧ seg.bus≠66)
    (j:Nat) (hj:j<4)
    (hm:tableBusCount (base j).interactions (source tr) j pub B_BYTES true msg≠0) :
    msg[0]!.toNat%16=13 := by
  apply logical_tag (local_logical hH htables hpub)
  rw [←bytes_count hH htables]
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
end ZkFormal.NearV3.Candidates.ProcPriorRoutedSourceByteTag
