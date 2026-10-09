import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicRow
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedIdBound ProcPriorRoutedFamilyId
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem raw_receivers:ProcPriorComparatorRoutedFamily.raw.interactions.filter
    (fun i=>i.bus==70 && !i.send)=[publicRead]:=rfl

theorem receiver_eq {i:Interaction} (hi:i∈ProcPriorComparatorRoutedFamily.fused.interactions)
    (hb:i.bus=70) (hs:i.send=false):i=publicRead:=by
  have hp:∀i∈ProcPriorComparatorRoutedFamily.paired.interactions,i.bus=70→i.send=false→i=publicRead:=by
    intro i hi hb hs
    have hm:i∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==70 && !i.send):=
      List.mem_filter.mpr ⟨(InteractionPairing.reorder_perm _).mem_iff.mp hi,by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    exact List.mem_singleton.mp hm
  exact ((InteractionTriples.forall_iff _ (fun i=>i.bus=70→i.send=false→i=publicRead)
    (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp) i hi hb hs

theorem other_tables {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr):
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=70→i.send=true:=by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != 70 || i.send)))=true:=by decide +kernel
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

theorem matched {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠70)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=70) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0):
    ∃q,q<tr.height 0 ∧ publicRead.multNat tr 0 q pub≠0 ∧
      publicRead.msgVal tr 0 q pub=i.msgVal tr t r pub:=by
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  obtain ⟨q,hq,k,hk,hkb,hks,hmsg,hkm⟩:=send_matched view.valid ht0 (other_tables view) hpub ht hr hi hb hs hm
  rw [view.wires] at hk
  have he:=receiver_eq hk hkb hks
  subst k
  exact ⟨q,hq,hkm,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver
