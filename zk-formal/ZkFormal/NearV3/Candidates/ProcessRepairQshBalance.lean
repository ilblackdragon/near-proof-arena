import ZkFormal.NearV3.Candidates.ProcessRepairKeyBalance
namespace ZkFormal.NearV3.Candidates.ProcessRepairQshBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Near Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fused_count (tr:Trace Fp) (pub msg:List Fp) (dir:Bool) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_QSH dir msg=
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_QSH dir msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_QSH && i.send==dir)=
      (Qv.Candidates.KeyTrafficRepair.interactions.filter (fun i=>i.bus==B_QSH && i.send==dir)).map
        (HorizontalTables.interaction ProcPriorRoutedKeyView.offset) := by cases dir <;> rfl
  rw [hraw,ProcPriorRoutedVParent.filter_count Qv.Candidates.KeyTrafficRepair.interactions]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedKeyView.offset)
    _ tr (ProcPriorRoutedKeyView.key tr) 0 pub B_QSH dir msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedKeyView.offset pub e)

theorem global_count {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) (dir:Bool) :
    busCount AP.toAir tr pub B_QSH dir msg=
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_QSH dir msg := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
    (fun T=>T.interactions.all (fun i=>i.bus != B_QSH)))=true:=by decide +kernel
  have ht:busCount.go tr pub B_QSH dir msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=0 := by
    apply busCount_go_zero
    intro t ht
    apply tableBusCount_zero
    intro i hi hb
    have hm:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1:=by
      rw [getElem!_pos (ProcPriorComparatorRoutedFamily.tables.drop 1) t ht];exact List.getElem_mem ht
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
    simpa [hb] using hh
  unfold busCount
  change busCount.go tr pub B_QSH dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_QSH dir msg+busCount.go tr pub B_QSH dir msg (ProcPriorComparatorRoutedFamily.tables.drop 1) 1=_
  rw [ht,Nat.add_zero,fused_count]

theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_QSH) (msg:List Fp) :
    tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_QSH true msg=
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_QSH false msg := by
  have h:=ProcessRepairBalance.balance view B_QSH msg
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_QSH dir msg=0:=
    pubCount_zero (fun seg hs hb=>absurd hb (hpub seg hs)) msg
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,global_count rfl,global_count rfl] at h
  exact h
end ZkFormal.NearV3.Candidates.ProcessRepairQshBalance
