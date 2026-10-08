import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedUpsertList

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Render.UpsGen Assembly

/-- The native allocation bounds hold for the actual receipt-updated UPS inputs,
not only the scheduler-before-receipts diagnostic executions. -/
theorem native_rebased_physical_bounds {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length≤31) (hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true) :
    ∃writes,∃oldPost : PTrie,∃us : List SchedulerUpsertWitness,
      SizedAccountRun m.pre writes oldPost ∧
      us.map (fun u=>(u.pre,u.run.output))=(oldPost,m.result.trie)::steps.map (fun s=>(s.pre,s.post)) ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u=>outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u=>u.value.length)).sum≤3146912 ∧
      let rs:=nativeReplayForest m steps oldPost writes
      (∀r∈rs,r.Valid) ∧
      (records (forestOldInputs rs) (forestNodes 0 0 0 (m.pre::steps.map ImplicitStepV3.pre))).map (fun s=>s.v.ser true)=
        ((rs.map ReplayTree.post).flatMap occs).map (fun t=>(nodeEnc t).map UInt8.toNat) := by
  have hc : checkD0 cb wb=.ok () := by
    unfold checkD0a at h
    obtain ⟨u,hu,_⟩:=ReexecV3D0.bind_ok' h
    cases u;exact hu
  have hL:=(checkD0_claim_guards hk hw hc).1.layout.2
  obtain ⟨writes,oldPost,us,hr,hpairs,hvalid,hforest,hbytes⟩:=native_rebased_upserts hm hv hL
  have he : us.map SchedulerUpsertWitness.pre=oldPost::steps.map ImplicitStepV3.pre := by
    have hh:=congrArg (List.map Prod.fst) hpairs
    simpa only [List.map_map,List.map_cons,Function.comp_def] using hh
  have hcount:=congrArg List.length he
  simp only [List.length_map,List.length_cons] at hcount
  have hmem : ∀u∈us,u.pre∈oldPost::steps.map ImplicitStepV3.pre := by
    intro u hu
    rw [←he]
    exact List.mem_map.mpr ⟨u,hu,rfl⟩
  have hwell : ∀u∈us,u.pre.wf=true := by
    intro u hu
    rcases List.mem_cons.mp (hmem u hu) with hp|hp
    · rw [hp]
      exact SizedAccountRun.wf hr (hwf _ (by simp))
    · exact hwf _ (by simp [hp])
  have hdepth : ∀u∈us,fdepth u.pre keyBwState≤400 := by
    intro u hu
    rcases List.mem_cons.mp (hmem u hu) with hp|hp
    · rw [hp,←write_lookup_depth hr.forget.skeleton,hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.2.2 _
    · obtain ⟨s,hs,hp⟩:=List.mem_map.mp hp
      obtain ⟨hpre,hroot,_⟩:=hv.input_facts s hs
      rw [←hp,hpre]
      exact (built_spec s.witness.values trieFuel s.root _ hroot).2.2.2 _
  have hb:=checkD0a_preBytes hk hw h hm hv
  have hb' : preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 := by
    rw [he]
    simpa only [preBytes,List.map_cons,List.sum_cons,SizedAccountRun.unfolded_bytes hr,B0] using hb
  have hout:=schedulerUpserts_output_tight_charge us (fun u hu=>(hvalid u hu).1) hwell
  have hval:=scheduler_value_sum us (fun u hu=>(hvalid u hu).2)
  refine ⟨writes,oldPost,us,hr,hpairs,by omega,by omega,?_,hb',by omega,by omega,hforest,hbytes⟩
  intro u hu
  have hp:=traceUpsert_count u.pre keyBwState u.value u.run (hvalid u hu).1.1
  exact ⟨(hvalid u hu).1,hwell u hu,by have hh:=hdepth u hu;omega,hdepth u hu,(hvalid u hu).2⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
