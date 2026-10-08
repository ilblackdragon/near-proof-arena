import ZkFormal.NearV3.Render.Ups.SchedulerShaInstances
import ZkFormal.NearV3.Render.Ups.ForestNativeWalkExact
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows Assembly ZkFormal.Near
def ExactNativeWalkProviders (pairs : List (PTrie×PTrie)) (run : TreeRun) (I : UpsInst) : Prop :=
  ∃ (a : OccurrenceAddress) (s : NodeS3) (h : HeadE),
    (forestStoreViews (pairs.map Prod.fst)).nodes[a.nid]?=some s ∧
    (forestWalkHeads 0 0 pairs)[I.tau]?=some h ∧
    (step I 0).e++[0]=startEdgeMsg h 0 ∧
    (∀ t,1≤t → t<I.ts → ∃ n provider,
      (forestStoreViews (pairs.map Prod.fst)).nodes[n]?=some provider ∧ (step I t).e∈edgesOf3 n provider) ∧
    ((step I I.ts).e).getD 0 0=a.nid ∧
    (((run.terminal=.BV ∨ run.terminal=.BI) ∧ s.v.bmap=some ((step I I.ts).bm,(step I I.ts).hv)) ∨
      (step I I.ts).e∈edgesOf3 a.nid s)

theorem scheduler_instance_exact_inputs {us : List SchedulerUpsertWitness}
    (hgood : ∀ u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧
      fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341)
    (hpre : preBytes (us.map SchedulerUpsertWitness.pre)≤2000000)
    (hout : (us.map (fun u=>outputByteCharge u.run)).sum≤2131072)
    {tau : Nat} {u : SchedulerUpsertWitness} (hu : us[tau]?=some u) {root : OccurrenceAddress}
    (hroot : forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root)
    (baseI : UpsInst) (base : Nat→UpsPartI) :
    ∃ I : UpsInst,I.tau=tau ∧ I.mid=baseI.mid ∧ I.post=baseI.post ∧ I.v=u.value.map UInt8.toNat ∧
      InstOk I ∧ ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧ (recsI I).length=4+u.value.length+outputByteCharge u.run ∧ NativePartFamily I ∧ NativeShaFamily u I := by
  have hum := List.mem_of_getElem? hu
  obtain ⟨hv,hw,hcount,hd,hvlen⟩ := hgood u hum
  have ht := forestRootAt_tree 0 0 (us.map SchedulerUpsertWitness.pre) tau
  rw [hroot,List.getElem?_map,hu] at ht
  have htree : root.tree=u.pre := Option.some.inj ht
  have hr : traceUpsert root.tree [0,15] u.value=some u.run := by
    simpa only [htree,keyBwState_nibbles] using hv.1
  obtain ⟨so,hsched,hvalue⟩ := hv.2
  have hf : root.tree.find [0,15]≠none := by
    simpa only [htree,keyBwState_nibbles] using schedStep_write_known hsched
  have hvpos : 1≤u.value.length := by
    have hl := SchedulerUpsertWitness.value_length hv
    omega
  let pairs := us.map (fun u=>(u.pre,u.run.output))
  have hpairs : pairs.map Prod.fst=us.map SchedulerUpsertWitness.pre := by simp [pairs,List.map_map]
  have hroot' : forestRootAt 0 0 (pairs.map Prod.fst) tau=some root := hpairs ▸ hroot
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨Qs,a,s,h,he,hs,hh,hi,hstart,hprefix,hterminalId,hterminal⟩ := forest_native_walk_exact hroot' hr hf
    (htree ▸ hw) hvpos (by omega) baseI (nativeSourceBase recordId u.run base)
  let B := nativeWalkBase recordId (fun _=>a.vid) (occurrenceResolvedId recordId)
    {baseI with tau:=tau} root.tree u.run u.value
  let I := nativeInstance recordId B root.tree u.run u.value Qs
  refine ⟨I,rfl,rfl,rfl,rfl,hi,⟨a,s,h,hs,hh,hstart,hprefix,hterminalId,hterminal⟩,?_,?_⟩
  · exact nativeInstance_rowCost recordId B root.tree u.run u.value _ he
  constructor
  · intro k hk
    have hn : nQ I=Qs.length := nativeInstance_nQ _ _ _ _ _ _
    have hbounds : k<Qs.length := hn ▸ hk
    have hparts := scheduler_partInputs hgood hpre hout hu hroot B base he k hbounds
    change Nonempty (ByteInput I (part I k)) ∧ FieldsOk (part I k) ∧ PartOk I k (part I k) ∧
      WindowOk I (part I k) ∧ MemOk I (part I k) ∧
      (part I k).jm-1<nQ I ∧ (part I k).clen=(child I (part I k)).q.length
    rw [hn]
    exact hparts
  · constructor
    · exact (nativeInstance_nQ _ _ _ _ _ _).trans (encodeNativeParts_length recordId hr _ he)
    · intro k hk
      have hn : nQ I=Qs.length := nativeInstance_nQ _ _ _ _ _ _
      exact nativeInstance_part_shaJob_exact recordId B hr (htree ▸ hw) _ he k (hn ▸ hk)
end ZkFormal.NearV3.Render.UpsGen
