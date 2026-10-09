import ZkFormal.NearV3.Candidates.ProcessRepairWriteStamp
import ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
import ZkFormal.NearV3.Candidates.ProcPriorVerticalWriteActivity
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryWriteConsumer
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.V2
open ZkFormal.NearV3.Sched ProcPriorRoutedWriteStamp
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem raw_receivers:ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==67 && !i.send)=[write]:=rfl
theorem receiver_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=67) (hs:i.send=false) :i=write := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=67→j.send=false→j=write := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==67 && !i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_receivers] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=67→j.send=false→j=write :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=67→j.send=false→j=write)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs


theorem other_tables {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr):
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.bus=67→i.send=true:=by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>i.bus != 67 || i.send)))=true:=by decide +kernel
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

/-- Every actual emitted record write is represented by a live memory write
with exactly the same payload; memory cannot omit a published write. -/
theorem matched {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠67)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=67) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0):
    ∃q,q<tr.height 0 ∧ ProcPriorVerticalLastWrite.Live (memory tr) 0 q ∧
      cv (memory tr) 0 q ProcPriorMemoryTable.query=0 ∧
      ProcPriorVerticalWriteActivity.write.msgVal (memory tr) 0 q pub=i.msgVal tr t r pub:=by
  have ht0:0<AP.tables.length:=by rw [view.length];decide +kernel
  obtain ⟨q,hq,j,hj,hjb,hjs,hmsg,hjm⟩:=send_matched view.valid ht0 (other_tables view) hpub ht hr hi hb hs hm
  rw [view.wires] at hj
  have he:=receiver_eq hj hjb hjs
  subst j
  rw [write_mult] at hjm
  rw [write_message] at hmsg
  obtain ⟨hst,ha,hquery⟩:=ProcPriorVerticalWriteActivity.flags (ProcessRepairMemoryOrder.local_memory view) hq hjm
  exact ⟨q,hq,⟨hst,ha⟩,hquery,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcessRepairMemoryWriteConsumer
