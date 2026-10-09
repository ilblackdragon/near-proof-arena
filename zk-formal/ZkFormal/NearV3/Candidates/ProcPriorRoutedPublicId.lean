import ZkFormal.NearV3.Candidates.ProcPriorRoutedCodecParameters
import ZkFormal.NearV3.Candidates.ProcPriorCodecPublicBound
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedPublicId
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedCodecProjection
set_option maxRecDepth 32767
set_option maxHeartbeats 1000000

def publicId : Interaction:=interaction ProcPriorCodecActual.publicId

theorem raw_senders :ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==70 && i.send)=[publicId] := rfl


theorem sender_eq {i : Interaction} (hi:i∈(ProcPriorComparatorRoutedFamily.tables[0]!).interactions)
    (hb:i.bus=70) (hs:i.send=true) :i=publicId := by
  have hp:∀j∈ProcPriorComparatorRoutedFamily.paired.interactions,j.bus=70→j.send=true→j=publicId := by
    intro j hj hb hs
    have hj':j∈ProcPriorComparatorRoutedFamily.raw.interactions :=
      (InteractionPairing.reorder_perm _).mem_iff.mp hj
    have hm:j∈ProcPriorComparatorRoutedFamily.raw.interactions.filter (fun i=>i.bus==70 && i.send) :=
      List.mem_filter.mpr ⟨hj',by simp [hb,hs]⟩
    rw [raw_senders] at hm
    exact List.mem_singleton.mp hm
  have hh:∀j∈InteractionTriples.reorder ProcPriorComparatorRoutedFamily.paired.interactions,
      j.bus=70→j.send=true→j=publicId :=
    (InteractionTriples.forall_iff _ (fun j=>j.bus=70→j.send=true→j=publicId)
      (by simp [InteractionTriples.dummy]) (by simp [InteractionTriples.dummy])).mpr hp
  exact hh i hi hb hs


theorem other_tables {AP : AirP}
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ∀t,t<AP.tables.length→t≠0→∀i∈AP.tables[t]!.interactions,i.send=true→i.bus≠70 := by
  have hall:((ProcPriorComparatorRoutedFamily.tables.drop 1).all
      (fun T=>T.interactions.all (fun i=>!i.send || i.bus != 70)))=true := by decide +kernel
  intro t ht hn i hi hs
  rw [htables] at ht hi
  have hm:ProcPriorComparatorRoutedFamily.tables[t]!∈ProcPriorComparatorRoutedFamily.tables.drop 1 := by
    have he:(ProcPriorComparatorRoutedFamily.tables.drop 1)[t-1]?=some (ProcPriorComparatorRoutedFamily.tables[t]!) := by
      rw [List.getElem?_drop]
      have he:1+(t-1)=t := by omega
      rw [he]
      rw [List.getElem?_eq_getElem ht]
      congr 1
      exact (getElem!_pos ProcPriorComparatorRoutedFamily.tables t ht).symm
    exact List.mem_iff_getElem?.mpr ⟨t-1,he⟩
  have hv:=List.all_eq_true.mp (List.all_eq_true.mp hall _ hm) i hi
  simpa [hs] using hv


end ZkFormal.NearV3.Candidates.ProcPriorRoutedPublicId
