import ZkFormal.NearV3.Candidates.AcceptedOriginWriteKeys
import ZkFormal.NearV3.Rcpt.Candidates.NativeWindowPhysicalCoverage
import ZkFormal.NearV3.Rcpt.Candidates.NativeWindowProviderInputs
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedPhysicalKeys
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Exact native old-record payloads and allocated rebased UPS readers share the
same forest, scheduler witnesses, occurrence indices and poststate targets. -/
theorem accepted_window_write_keys {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,∃insts : List UpsInst,
      writes.map Prod.fst=(appliedReceipts k w).map (fun r=>accountKeyPath r.receiverId) ∧
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      insts.length=us.length ∧
      (∀tau u I,us[tau]?=some u→insts[tau]?=some I→
        AllocatedNativeInstance us tau u I ∧ NativeShaFamily u I ∧
        ExactNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        I.ci=u.run.terminal.ix ∧ DispatchNativeWalkProviders (us.map (fun u=>(u.pre,u.run.output))) u.run I ∧
        ∃root,forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
          NativeReaderOrigin root u.run u.value I) ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) ∧
      ∀t r,r∈physicalWindowRows (Candidates.CompactHeight.trace insts) t→
        physicalWindowKey (Candidates.CompactHeight.trace insts) t r∈nodeWindowKeys
          (records (forestOldInputs rs) (initializeList 0 (forestNodes 0 0 0 (rs.map ReplayTree.pre)))) := by
  obtain ⟨writes,oldPost,us,insts,hkeys,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes⟩:=
    accepted_origin_write_keys hk hw h hm hv baseI base
  let rs:=nativeReplayForest m steps oldPost writes
  have hpreEq : us.map SchedulerUpsertWitness.pre=rs.map ReplayTree.post := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa [rs,nativeReplayForest,List.map_map,Function.comp_def] using hh
  have hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  have hrs : rs.map ReplayTree.pre=m.pre::steps.map ImplicitStepV3.pre := by
    simp [rs,nativeReplayForest,List.map_map,Function.comp_def]
  have hwr : ∀r∈rs,r.pre.wf=true := by
    intro r hr
    exact hwf _ (hrs ▸ List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hn:=native_window_provider_ok hk hw h hm hv (forestOldInputs rs)
  have hb:=native_window_provider_bytes (m.pre::steps.map ImplicitStepV3.pre) hwf (forestOldInputs rs)
  refine ⟨writes,oldPost,us,insts,hkeys,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes,?_⟩
  intro t
  apply native_physical_window_coverage rs hforest hwr (hpreEq ▸ hpre) us insts hpreEq
    (fun u hu=>⟨(hgood u hu).1,(hgood u hu).2.1⟩) hcount
  · intro tau u I hu hI
    obtain ⟨a,sha,exactp,ci,dispatch,root,hroot,origin⟩:=hinst tau u I hu hI
    exact ⟨a,root,hroot,origin⟩
  · simpa only [hrs] using hn.wf
  · intro s hs x hx
    rw [hrs] at hs
    exact hb s hs true x hx

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
