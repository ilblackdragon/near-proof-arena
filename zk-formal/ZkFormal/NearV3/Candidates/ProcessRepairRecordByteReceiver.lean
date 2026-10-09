import ZkFormal.NearV3.Candidates.ProcessRepairRecordByteSource
namespace ZkFormal.NearV3.Candidates.ProcessRepairRecordByteReceiver
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRecordPhysicalBytes
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem raw_receivers:ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==75 && !i.send)=[request 0,request 1,request 2]:=rfl

theorem receiver_index {i:Interaction} (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hb:i.bus=75) (hs:i.send=false):∃j,j<3 ∧ i=request j:=by
  have hp:∀i∈ProcPriorComparatorRoutedFamily.paired.interactions,i.bus=75→i.send=false→∃j,j<3 ∧ i=request j:=by
    intro i hi hb hs
    have hm:i∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==75 && !i.send):=
      List.mem_filter.mpr ⟨(InteractionPairing.reorder_perm _).mem_iff.mp hi,by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h|h|h
    · exact ⟨0,by decide,h⟩
    · exact ⟨1,by decide,h⟩
    · exact ⟨2,by decide,h⟩
  exact ((InteractionTriples.forall_iff _ (fun i=>i.bus=75→i.send=false→∃j,j<3 ∧ i=request j)
    (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp) i hi hb hs

theorem other_tables {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr):
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=75→i.send=true:=by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != 75 || i.send)))=true:=by decide +kernel
  intro t ht hn i hi hb
  rw [view.wires] at hi
  have hlen:t<ProcPriorComparatorRoutedFamily.tables.length:=by rw [←view.length];exact ht
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1:=by
    apply List.mem_iff_getElem?.mpr
    refine ⟨t-1,?_⟩
    rw [List.getElem?_drop,show 1+(t-1)=t by omega,List.getElem?_eq_getElem hlen]
    congr 1
    exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t hlen).symm
  have h:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hb] using h

/-- Every live raw-record byte supplier has an actual physical record-byte
consumer. This is the reverse direction needed to exclude omitted records. -/
theorem matched {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠75)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=75) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0):
    ∃q j,q<tr.height 0 ∧ j<3 ∧ (request j).multNat tr 0 q pub≠0 ∧
      (request j).msgVal tr 0 q pub=i.msgVal tr t r pub:=by
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  obtain ⟨q,hq,k,hk,hkb,hks,hmsg,hkm⟩:=send_matched view.valid ht0 (other_tables view) hpub ht hr hi hb hs hm
  rw [view.wires] at hk
  obtain ⟨j,hj,rfl⟩:=receiver_index hk hkb hks
  exact ⟨q,j,hq,hj,hkm,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairRecordByteReceiver
