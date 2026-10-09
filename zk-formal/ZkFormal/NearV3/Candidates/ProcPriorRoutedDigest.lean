import ZkFormal.NearV3.Candidates.ProcPriorRoutedShaFacts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedRootCounts
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Chacha
open ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

def dig:Interaction:=(ShaCarryKinds.table B_BYTES B_DIGEST).interactions[16]!
def shifted (j:Nat):Interaction:=HorizontalTables.interaction (ProcPriorRoutedShaView.offset j) dig

theorem component_count (tr:Trace Fp) (pub msg:List Fp) (j:Nat) :
    tableBusCount [shifted j] tr 0 pub B_DIGEST true msg=
      ProcPriorRoutedShaFacts.count tr pub j true B_DIGEST msg := by
  unfold ProcPriorRoutedShaFacts.count
  rw [ProcPriorRoutedVParent.filter_count (ShaCarryKinds.table B_BYTES B_DIGEST).interactions]
  have he:(ShaCarryKinds.table B_BYTES B_DIGEST).interactions.filter
      (fun i=>i.bus==B_DIGEST && i.send==true)=[dig] := rfl
  rw [he]
  exact HorizontalTraffic.count_map (HorizontalTables.expression (ProcPriorRoutedShaView.offset j))
    [dig] tr (ProcPriorRoutedShaView.sha j tr) 0 pub B_DIGEST true msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r _ pub e)

def empty:Interaction:=HorizontalTables.interaction ProcPriorRoutedRawBytes.valueOffset
  Rcpt.Candidates.EmptyValue.emptyInteraction

def emptyCount (tr:Trace Fp) (pub msg:List Fp):Nat:=tableBusCount [empty] tr 0 pub B_DIGEST true msg

theorem fused_count (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_DIGEST true msg=
      ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] true B_DIGEST msg+emptyCount tr pub msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have he:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_DIGEST && i.send==true)=
      [shifted 0]++[shifted 1]++[shifted 2]++[shifted 3]++[empty] := rfl
  rw [he]
  simp only [HorizontalTraffic.count_append,component_count,ProcPriorRoutedShaFacts.sumCount,Nat.add_zero,emptyCount]
  omega

theorem tail_no_sender :((ProcPriorComparatorRoutedFamily.tables.drop 1).all
    (fun T=>T.interactions.all (fun i=>!(i.bus==B_DIGEST && i.send))))=true := by decide +kernel

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) :
    busCount AP.toAir tr pub B_DIGEST true msg=
      ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] true B_DIGEST msg+emptyCount tr pub msg := by
  have htail:busCount.go tr pub B_DIGEST true msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=0 := by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hb
    have hmem:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 1) t ht];exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp tail_no_sender _ hmem) i hi
    simpa [hb] using hh
  unfold busCount
  change busCount.go tr pub B_DIGEST true msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_DIGEST true msg+busCount.go tr pub B_DIGEST true msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1= _
  rw [htail,Nat.add_zero,fused_count]
end ZkFormal.NearV3.Candidates.ProcPriorRoutedDigest
