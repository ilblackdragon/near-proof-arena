import ZkFormal.NearV3.Candidates.ProcPriorRoutedUpsView
import ZkFormal.NearV3.Candidates.ProcPriorRoutedParent
import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsChain
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedRootCounts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.Near
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem ups_count (tr:Trace Fp) (pub msg:List Fp) (dir:Bool) (b:Nat) (hb:b=B_ROOT ∨ b=B_MIDROOT) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub b dir msg=
      tableBusCount Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub b dir msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==b && i.send==dir)=
      (Render.UpsRelay.compactInteractions.filter (fun i=>i.bus==b && i.send==dir)).map
        (HorizontalTables.interaction ProcPriorRoutedUpsView.offset) := by
    rcases hb with rfl | rfl <;> cases dir <;> rfl
  rw [hraw,ProcPriorRoutedVParent.filter_count Render.UpsRelay.compactInteractions]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedUpsView.offset)
    _ tr (ProcPriorRoutedUpsView.ups tr) 0 pub b dir msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedUpsView.offset pub e)

theorem tail_absent (b:Nat) (hb:b=B_ROOT ∨ b=B_MIDROOT) :((ProcPriorComparatorRoutedFamily.tables.drop 2).all
    (fun T=>T.interactions.all (fun i=>i.bus != b)))=true := by rcases hb with rfl | rfl <;> decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (dir:Bool) (msg:List Fp) (b:Nat) (hb:b=B_ROOT ∨ b=B_MIDROOT) :
    busCount AP.toAir tr pub b dir msg=
      tableBusCount Render.UpsRelay.compactInteractions (ProcPriorRoutedUpsView.ups tr) 0 pub b dir msg+
      tableBusCount HeadV3.interactions tr 1 pub b dir msg := by
  have htail:busCount.go tr pub b dir msg (ProcPriorComparatorRoutedFamily.tables.drop 2) 2=0 := by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hbus
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 2)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 2 := by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 2) t ht]
      exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp (tail_absent b hb) _ hmem) i hi
    have hn:i.bus≠b := by simpa using hh
    exact (hn hbus).elim
  unfold busCount
  change busCount.go tr pub b dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub b dir msg+
    (tableBusCount (InteractionTriples.table HeadV3.table).interactions tr 1 pub b dir msg+
      busCount.go tr pub b dir msg (ProcPriorComparatorRoutedFamily.tables.drop 2) 2)=_
  rw [htail,Nat.add_zero,ups_count tr pub msg dir b hb]
  change _+tableBusCount (InteractionTriples.reorder HeadV3.interactions) tr 1 pub b dir msg=_
  rw [InteractionTriples.count]

end ZkFormal.NearV3.Candidates.ProcPriorRoutedRootCounts
