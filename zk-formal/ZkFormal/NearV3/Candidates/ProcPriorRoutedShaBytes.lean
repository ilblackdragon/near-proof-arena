import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRootCounts
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedShaBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def bytes:List Interaction:=(ShaCarryKinds.table B_BYTES B_DIGEST).interactions.filter
  (fun i=>i.bus==B_BYTES && i.send==false)
def shifted (j:Nat):List Interaction:=bytes.map
  (HorizontalTables.interaction (ProcPriorRoutedShaView.offset j))

theorem component_count (tr:Trace Fp) (pub msg:List Fp) (j:Nat) :
    tableBusCount (shifted j) tr 0 pub B_BYTES false msg=
      ProcPriorRoutedShaFacts.count tr pub j false B_BYTES msg := by
  unfold ProcPriorRoutedShaFacts.count
  rw [ProcPriorRoutedVParent.filter_count (ShaCarryKinds.table B_BYTES B_DIGEST).interactions]
  exact HorizontalTraffic.count_map (HorizontalTables.expression (ProcPriorRoutedShaView.offset j))
    bytes tr (ProcPriorRoutedShaView.sha j tr) 0 pub B_BYTES false msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)

theorem fused_count (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_BYTES false msg=
      ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false B_BYTES msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have he:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_BYTES && i.send==false)=
      shifted 0++shifted 1++shifted 2++shifted 3 := rfl
  rw [he]
  simp only [HorizontalTraffic.count_append,component_count,ProcPriorRoutedShaFacts.sumCount,Nat.add_zero]
  omega

theorem tail_no_receiver :(HorizontalAccounts.rest.all
    (fun T=>T.interactions.all (fun i=>!(i.bus==B_BYTES && !i.send))))=true := by decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) :
    busCount AP.toAir tr pub B_BYTES false msg=
      ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false B_BYTES msg := by
  have htail:busCount.go tr pub B_BYTES false msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=0 := by
    apply busCount_go_zero
    intro t ht
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 1) t ht];exact List.getElem_mem ht
    change _∈HorizontalAccounts.rest.map InteractionTriples.table at hmem
    obtain ⟨T,hT,hEq⟩:=List.mem_map.mp hmem
    rw [←hEq]
    change tableBusCount (InteractionTriples.reorder T.interactions) _ _ _ _ _ _=0
    rw [InteractionTriples.count]
    apply tableBusCount_zero
    intro i hi hb
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp tail_no_receiver _ hT) i hi
    simpa [hb] using hh

  unfold busCount
  change busCount.go tr pub B_BYTES false msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_BYTES false msg+busCount.go tr pub B_BYTES false msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1= _
  rw [htail,Nat.add_zero,fused_count]
end ZkFormal.NearV3.Candidates.ProcPriorRoutedShaBytes
