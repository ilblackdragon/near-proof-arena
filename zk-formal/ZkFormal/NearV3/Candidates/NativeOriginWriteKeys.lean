import ZkFormal.NearV3.Rcpt.Candidates.ChosenReaderOrigins
import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedPhysicalKeys
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen UpsRows Assembly

/-- Exact native old-record payloads and allocated rebased UPS readers share the
same forest, scheduler witnesses, occurrence indices and poststate targets. -/
theorem native_origin_write_keys {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length≤31) (hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true)
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
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  obtain ⟨writes,oldPost,us,hkeys,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hforest,hbytes⟩:=
    native_rebased_physical_bounds_keys hk hw h hm hv hlen hwf
  obtain ⟨insts,hcount,hinst⟩:=chosen_origin_instances hgood hpre hout baseI base
  exact ⟨writes,oldPost,us,insts,hkeys,hr,hpairs,hpos,hlen,hgood,hpre,hout,hval,hcount,hinst,hforest,hbytes⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
