import ZkFormal.NearV3.Candidates.ProcessRepairQshBalance
import ZkFormal.NearV3.Candidates.ProcessRepairRawStartClosed
namespace ZkFormal.NearV3.Candidates.ProcessRepairVbytesCounts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Near Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fused_send (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VBYTES true msg=
      tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_VBYTES true msg+
      tableBusCount [ProcPriorRoutedRawBytes.bytes] tr 0 pub B_VBYTES true msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_VBYTES && i.send==true)=
      (Qv.Candidates.KeyTrafficRepair.interactions.filter (fun i=>i.bus==B_VBYTES && i.send==true)).map
        (HorizontalTables.interaction ProcPriorRoutedKeyView.offset) ++ [ProcPriorRoutedRawBytes.bytes] := rfl
  rw [hraw,HorizontalTraffic.count_append,ProcPriorRoutedVParent.filter_count Qv.Candidates.KeyTrafficRepair.interactions]
  congr 1

theorem fused_recv (tr:Trace Fp) (pub msg:List Fp) :
    tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VBYTES false msg=
      tableBusCount ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub B_VBYTES false msg := by
  change tableBusCount (InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions) _ _ _ _ _ _=_
  rw [InteractionTriples.count]
  change tableBusCount (InteractionPairing.reorder ProcPriorComparatorRoutedFamily.raw.interactions) _ _ _ _ _ _=_
  rw [InteractionPairing.count,ProcPriorRoutedVParent.filter_count]
  have hraw:ProcPriorComparatorRoutedFamily.raw.interactions.filter
      (fun i=>i.bus==B_VBYTES && i.send==false)=
      (ValV3.interactions.filter (fun i=>i.bus==B_VBYTES && i.send==false)).map
        (HorizontalTables.interaction ProcPriorRoutedRawBytes.valueOffset) := rfl
  rw [hraw,ProcPriorRoutedVParent.filter_count ValV3.interactions]
  exact HorizontalTraffic.count_map (HorizontalTables.expression ProcPriorRoutedRawBytes.valueOffset)
    _ tr (ProcPriorRoutedRawBytes.value tr) 0 pub B_VBYTES false msg rfl
    (by intro r i hi e he;exact HorizontalTrace.expression_eval tr 0 r ProcPriorRoutedRawBytes.valueOffset pub e)

theorem global_counts {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) (msg:List Fp) (dir:Bool) :
    busCount AP.toAir tr pub B_VBYTES dir msg=
      tableBusCount ProcPriorComparatorRoutedFamily.fused.interactions tr 0 pub B_VBYTES dir msg+
      tableBusCount AcctV3.interactions tr 6 pub B_VBYTES dir msg+
      tableBusCount AkeyV3.interactions tr 7 pub B_VBYTES dir msg := by
  have hall:(ProcPriorComparatorRoutedFamily.tables.zipIdx.all
    (fun p=>p.1.interactions.all (fun i=>i.bus != B_VBYTES || p.2==0 || p.2==6 || p.2==7)))=true:=by decide +kernel
  have hz (t:Nat) (ht:t<ProcPriorComparatorRoutedFamily.tables.length) (h0:t≠0) (h6:t≠6) (h7:t≠7):
      tableBusCount ProcPriorComparatorRoutedFamily.tables[t]!.interactions tr t pub B_VBYTES dir msg=0:=by
    apply tableBusCount_zero
    intro i hi hb
    have hm:(ProcPriorComparatorRoutedFamily.tables[t],t)∈ProcPriorComparatorRoutedFamily.tables.zipIdx:=by
      apply List.mem_iff_getElem?.mpr
      exact ⟨t,by simp [List.getElem?_zipIdx,List.getElem?_eq_getElem ht]⟩
    have hh:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i
      (by simpa only [getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht] using hi)
    simpa [hb,h0,h6,h7] using hh
  unfold busCount
  change busCount.go tr pub B_VBYTES dir msg AP.tables 0=_
  rw [htables]
  change tableBusCount ProcPriorComparatorRoutedFamily.tables[0]!.interactions tr 0 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[1]!.interactions tr 1 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[2]!.interactions tr 2 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[3]!.interactions tr 3 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[4]!.interactions tr 4 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[5]!.interactions tr 5 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[6]!.interactions tr 6 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[7]!.interactions tr 7 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[8]!.interactions tr 8 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[9]!.interactions tr 9 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[10]!.interactions tr 10 pub B_VBYTES dir msg+(tableBusCount ProcPriorComparatorRoutedFamily.tables[11]!.interactions tr 11 pub B_VBYTES dir msg+(0))))))))))))=_
  rw [hz 1 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 2 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 3 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 4 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 5 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 8 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 9 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 10 (by decide +kernel) (by decide) (by decide) (by decide),
    hz 11 (by decide +kernel) (by decide) (by decide) (by decide)]
  simp only [Nat.zero_add,Nat.add_zero]
  change _+(tableBusCount (InteractionTriples.reorder AcctV3.interactions) tr 6 pub B_VBYTES dir msg+
    tableBusCount (InteractionTriples.reorder AkeyV3.interactions) tr 7 pub B_VBYTES dir msg)=_
  rw [InteractionTriples.count,InteractionTriples.count,Nat.add_assoc]
  rfl

theorem balance {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES) (msg:List Fp) :
    tableBusCount Qv.Candidates.KeyTrafficRepair.interactions (ProcPriorRoutedKeyView.key tr) 0 pub B_VBYTES true msg+
      tableBusCount [ProcPriorRoutedRawBytes.bytes] tr 0 pub B_VBYTES true msg+
      tableBusCount AcctV3.interactions tr 6 pub B_VBYTES true msg+
      tableBusCount AkeyV3.interactions tr 7 pub B_VBYTES true msg=
      tableBusCount ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub B_VBYTES false msg := by
  have h:=ProcessRepairBalance.balance view B_VBYTES msg
  have hp (dir:Bool):pubCount (ProcessRepairBalance.reference AP) pub B_VBYTES dir msg=0:=
    pubCount_zero (fun seg hs hb=>absurd hb (hpub seg hs)) msg
  have hz (is:List Interaction) (t:Nat) (hall:is.all (fun i=>i.bus != B_VBYTES || i.send)=true):
      tableBusCount is tr t pub B_VBYTES false msg=0:=by
    apply tableBusCount_zero
    intro i hi hb
    have hh:=List.all_eq_true.mp hall i hi
    simpa [hb] using hh
  rw [hp true,hp false,Nat.add_zero,Nat.add_zero,global_counts rfl,global_counts rfl,
    fused_send,fused_recv,hz AcctV3.interactions 6 (by decide +kernel),
    hz AkeyV3.interactions 7 (by decide +kernel),Nat.add_zero] at h
  exact h
end ZkFormal.NearV3.Candidates.ProcessRepairVbytesCounts
