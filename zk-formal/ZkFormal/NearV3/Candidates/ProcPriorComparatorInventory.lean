import ZkFormal.NearV3.Candidates.ProcPriorCodecFamilyRead
namespace ZkFormal.NearV3.Candidates.ProcPriorComparatorInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.NearV3.Sched
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Concrete receiver audit of the current corrected family. Bus69 has no
receiving interaction; it is not the installed scheduler comparator bus40. -/
theorem no_receivers :ProcPriorCodecActualFamily.tables.all
    (fun T=>T.interactions.all (fun i=>i.bus != 69 || i.send))=true := by decide +kernel

theorem receiver_absent {AP : AirP} (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    {t : Nat} (ht:t<AP.tables.length) {i : Interaction} (hi:i∈AP.tables[t]!.interactions)
    (hb:i.bus=69) :i.send=true := by
  have hm:AP.tables[t]!∈ProcPriorCodecActualFamily.tables := by
    rw [←htables,getElem!_pos AP.tables t ht]
    exact List.getElem_mem ht
  have he:=List.all_eq_true.mp (List.all_eq_true.mp no_receivers _ hm) i hi
  simpa [hb] using he

/-- With no public bus69 segments, actual-family balance forbids every live
prior comparison send. Thus ordinary multirow prior memory/ID execution
cannot be completed by this unpatched family, irrespective of order bounds. -/
theorem live_send_impossible {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorCodecActualFamily.tables)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠69)
    {t r : Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i : Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=69) (hs:i.send=true)
    (hm:i.multNat tr t r pub≠0) :False := by
  obtain ⟨r',hr',i',hi',hb',hs',_,_⟩:=send_matched hH ht
    (fun t ht _ i hi hb=>receiver_absent htables ht hi hb) hpub ht hr hi hb hs hm
  have he:=receiver_absent htables ht hi' hb'
  rw [he] at hs'
  contradiction
end ZkFormal.NearV3.Candidates.ProcPriorComparatorInventory
