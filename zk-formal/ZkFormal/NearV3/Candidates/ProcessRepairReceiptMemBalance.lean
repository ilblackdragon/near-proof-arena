import ZkFormal.NearV3.Candidates.ProcessRepairVbytesCounts
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinal
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemBalance
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Near Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fused (tr:Trace Fp) (pub msg:List Fp) (dir:Bool):
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_MEM dir msg=
      tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_MEM dir msg:=by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_MEM && i.send==dir)=
      (RcptV3.interactions.filter (fun i=>i.bus==B_MEM && i.send==dir)).map
        (HorizontalTables.interaction ProcPriorRoutedReceiptView.offset):=by cases dir <;> rfl
  rw [hraw,ProcPriorRoutedVParent.filter_count RcptV3.interactions]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedReceiptView.offset)
    _ tr (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_MEM dir msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedReceiptView.offset pub e)

theorem global_counts {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) (dir:Bool) :
    busCount AP.toAir tr pub B_MEM dir msg=
      tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_MEM dir msg+
      tableBusCount AcctV3.interactions tr 6 pub B_MEM dir msg := by
  have hall:(ProcPriorComparatorRoutedFamily.tables.zipIdx.all
    (fun p=>p.1.interactions.all (fun i=>i.bus != B_MEM || p.2==0 || p.2==6)))=true:=by decide +kernel
  have hz (t:Nat) (ht:t<ProcPriorComparatorRoutedFamily.tables.length) (h0:t≠0) (h6:t≠6):
      tableBusCount ProcPriorComparatorRoutedFamily.tables[t]!.interactions tr t pub B_MEM dir msg=0:=by
    apply tableBusCount_zero
    intro i hi hb
    have hm:(ProcPriorComparatorRoutedFamily.tables[t],t)∈ProcPriorComparatorRoutedFamily.tables.zipIdx:=by
      apply List.mem_iff_getElem?.mpr
      exact ⟨t,by simp [List.getElem?_zipIdx,List.getElem?_eq_getElem ht]⟩
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i
      (by simpa only [getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht] using hi)
    simpa [hb,h0,h6] using hh
  unfold busCount
  change busCount.go tr pub B_MEM dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.tables[0]!.interactions tr 0 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[1]!.interactions tr 1 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[2]!.interactions tr 2 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[3]!.interactions tr 3 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[4]!.interactions tr 4 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[5]!.interactions tr 5 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[6]!.interactions tr 6 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[7]!.interactions tr 7 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[8]!.interactions tr 8 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[9]!.interactions tr 9 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[10]!.interactions tr 10 pub B_MEM dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[11]!.interactions tr 11 pub B_MEM dir msg+(0))))))))))))=_
  rw [hz 1 (by decide +kernel) (by decide) (by decide),
    hz 2 (by decide +kernel) (by decide) (by decide),
    hz 3 (by decide +kernel) (by decide) (by decide),
    hz 4 (by decide +kernel) (by decide) (by decide),
    hz 5 (by decide +kernel) (by decide) (by decide),
    hz 7 (by decide +kernel) (by decide) (by decide),
    hz 8 (by decide +kernel) (by decide) (by decide),
    hz 9 (by decide +kernel) (by decide) (by decide),
    hz 10 (by decide +kernel) (by decide) (by decide),
    hz 11 (by decide +kernel) (by decide) (by decide)]
  simp only [Nat.zero_add,Nat.add_zero]
  change _+tableBusCount (InteractionTriples.reorder AcctV3.interactions) tr 6 pub B_MEM dir msg=_
  rw [InteractionTriples.count]
  rfl

theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_MEM) (msg:List Fp):
    tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_MEM true msg+
      tableBusCount AcctV3.interactions tr 6 pub B_MEM true msg=
    tableBusCount RcptV3.interactions (ProcPriorRoutedReceiptView.receipt tr) 0 pub B_MEM false msg+
      tableBusCount AcctV3.interactions tr 6 pub B_MEM false msg:=by
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_MEM dir msg=0:=
    pubCount_zero (fun seg hs hb=>absurd hb (hpub seg hs)) msg
  have h:=ProcessRepairBalance.balance view B_MEM msg
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,global_counts rfl,global_counts rfl,fused,fused] at h
  exact h
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptMemBalance
