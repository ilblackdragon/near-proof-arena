import ZkFormal.NearV3.Render.Ups.NativePrefixBounds
import ZkFormal.NearV3.Assembly.SchedulerAllBounds
import ZkFormal.NearV3.Assembly.UpsertPointwiseCost
import ZkFormal.NearV3.Assembly.UpsertSourcePointwise

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows Assembly

theorem forestRootAt_tree : ∀ n vid ts tau,
    (forestRootAt n vid ts tau).map OccurrenceAddress.tree=ts[tau]?
  | _,_,[],_ => by simp [forestRootAt]
  | _,_,_::_,0 => rfl
  | n,vid,t::ts,tau+1 => forestRootAt_tree (n+tsize t) (vid+(valsOf t).length) ts tau

/-- Actual accepted scheduler budgets discharge every numeric per-part bound.
The supplied run is the same operational witness charged by those budgets. -/
theorem scheduler_partInputs {us : List SchedulerUpsertWitness}
    (hgood : ∀ u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧
      fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341)
    (hpre : preBytes (us.map SchedulerUpsertWitness.pre)≤2000000)
    (hout : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072)
    {tau : Nat} {u : SchedulerUpsertWitness} (hu : us[tau]?=some u) {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root)
    (baseI : UpsInst) (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree u.run
      (nativeSourceBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) u.run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length) :
    let I := nativeInstance
      (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) baseI root.tree u.run u.value Qs
    Nonempty (ByteInput I (part I k)) ∧ FieldsOk (part I k) ∧ PartOk I k (part I k) ∧
      WindowOk I (part I k) ∧ MemOk I (part I k) ∧
      (part I k).jm-1<Qs.length ∧ (part I k).clen=(child I (part I k)).q.length := by
  have hum := List.mem_of_getElem? hu
  obtain ⟨hv,hw,hcount,hd,hvlen⟩ := hgood u hum
  have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) tau
  rw [hroot,List.getElem?_map,hu] at ht
  have htree : root.tree=u.pre := Option.some.inj ht
  have hr : traceUpsert root.tree [0,15] u.value=some u.run := by simpa only [htree,keyBwState_nibbles] using hv.1
  have hrwf : root.tree.wf=true := htree ▸ hw
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨p,hp,hq,hpref⟩ := nativeInstance_prefix_nativeLengths recordId baseI hr hrwf
    (nativeSourceBase recordId u.run base) he k hbound
  have ho := scheduler_part_length_bound hout hum (List.mem_of_getElem? hp)
  have hs := scheduler_source_length_bound hpre hum hv (List.mem_of_getElem? hp)
  apply nativeInstance_partInputs hroot hr hrwf (by omega) (by simpa only [htree,keyBwState_nibbles] using hd) baseI base he k hbound
  · exact Nat.lt_of_le_of_lt hq ho
  · exact Nat.lt_of_le_of_lt hpref hs
end ZkFormal.NearV3.Render.UpsGen
