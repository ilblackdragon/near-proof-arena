import ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsChain
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyCounts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.Near
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fused_count (tr:Trace Fp) (pub msg:List Fp) (dir:Bool) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_KEYNIB dir msg=
      tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB dir msg+
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_KEYNIB dir msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_KEYNIB && i.send==dir)=
      (RcptV3.interactions.filter (fun i=>i.bus==B_KEYNIB && i.send==dir)).map
        (HorizontalTables.interaction ProcPriorRoutedReceiptView.offset) ++
      (Qv.Candidates.KeyTrafficRepair.interactions.filter (fun i=>i.bus==B_KEYNIB && i.send==dir)).map
        (HorizontalTables.interaction ProcPriorRoutedKeyView.offset) := by
    cases dir <;> rfl
  rw [hraw,HorizontalTraffic.count_append]
  refine congr (congrArg Nat.add ?_) ?_
  · rw [ProcPriorRoutedVParent.filter_count RcptV3.interactions]
    exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedReceiptView.offset)
      _ tr (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB dir msg rfl
      (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedReceiptView.offset pub e)
  · rw [ProcPriorRoutedVParent.filter_count Qv.Candidates.KeyTrafficRepair.interactions]
    exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedKeyView.offset)
      _ tr (ProcPriorRoutedKeyView.key tr) 0 pub B_KEYNIB dir msg rfl
      (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedKeyView.offset pub e)
theorem tail_no_sender :((ProcPriorComparatorRoutedFamily.tables.drop 1).all
    (fun T=>T.interactions.all (fun i=>!(i.bus==B_KEYNIB && i.send))))=true := by decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) :
    busCount AP.toAir tr pub B_KEYNIB true msg=
      tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB true msg+
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_KEYNIB true msg := by
  have htail:busCount.go tr pub B_KEYNIB true msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=0 := by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hb
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 1) t ht];exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp tail_no_sender _ hmem) i hi
    simpa [hb] using hh
  unfold busCount
  change busCount.go tr pub B_KEYNIB true msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_KEYNIB true msg+busCount.go tr pub B_KEYNIB true msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1= _
  rw [htail,Nat.add_zero,fused_count tr pub msg true]
theorem query_source {AP:AirP} {tr:Trace Fp} {pub msg:List Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:pubCount AP pub B_KEYNIB true msg=0)
    (hc:0<tableBusCount WalkV3.interactions tr 2 pub B_KEYNIB false msg) :
    0<tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_KEYNIB true msg ∨
    0<tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_KEYNIB true msg := by
  have ht:2<AP.tables.length:=by rw [htables];decide +kernel
  have hle:=busCount_go_ge tr pub B_KEYNIB false msg AP.tables 0 2 ht
  simp only [Nat.zero_add] at hle
  have he:AP.tables[2]! =InteractionTriples.table WalkV3.table:=by rw [htables];rfl
  rw [he] at hle
  change tableBusCount (InteractionTriples.reorder WalkV3.interactions) tr 2 pub B_KEYNIB false msg≤_ at hle
  rw [InteractionTriples.count] at hle
  change _≤busCount AP.toAir tr pub B_KEYNIB false msg at hle
  have hh:=hH.balance B_KEYNIB msg
  rw [hpub,global_count htables] at hh
  omega
end ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyCounts
