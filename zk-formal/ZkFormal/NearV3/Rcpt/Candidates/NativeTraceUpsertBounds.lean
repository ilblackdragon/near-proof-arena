import ZkFormal.NearV3.Assembly.SchedulerSizedWitness

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Render.UpsGen Assembly

private theorem output_cost_arithmetic (a b c : Nat) (hb : b≤2000000) (hc : c≤32)
    (ha : a≤b+4096*c) : a≤2131072 := by omega

/-- Retains the exact chosen native prestate list, rather than selecting an
unrelated existential execution. Scheduler outputs need not equal final posts. -/
theorem native_trace_upsert_all_bounds {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hlen : steps.length≤31)
    (hwf : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true) :
    ∃ us : List SchedulerUpsertWitness,
      us.map SchedulerUpsertWitness.pre=m.pre::steps.map ImplicitStepV3.pre ∧
      1≤us.length ∧ us.length≤32 ∧
      (∀ u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403 ∧ fdepth u.pre keyBwState≤400 ∧ u.value.length≤98341) ∧
      preBytes (us.map SchedulerUpsertWitness.pre)≤2000000 ∧
      (us.map (fun u => outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u => u.value.length)).sum≤3146912 := by
  have hc : checkD0 cb wb=.ok () := by
    unfold checkD0a at h
    obtain ⟨u,hu,_⟩ := ReexecV3D0.bind_ok' h
    cases u; exact hu
  have hL := (checkD0_claim_guards hk hw hc).1.layout.2
  obtain ⟨u,hu,huv,hub⟩ := applyNewChunk_sized_witness hm.run hL
  obtain ⟨us,hus,husv⟩ := hv.sized_upserts hL
  have he : (u::us).map SchedulerUpsertWitness.pre=m.pre::steps.map ImplicitStepV3.pre := by simp [hu,hus]
  have hvalid : ∀ x∈u::us,x.Valid ∧ x.value.length≤98341 := by
    intro x hx; rcases List.mem_cons.mp hx with rfl|hx
    exact ⟨huv,hub⟩
    exact husv x hx
  have hmem : ∀ x∈u::us,x.pre∈m.pre::steps.map ImplicitStepV3.pre := by
    intro x hx; rw [←he]; exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hwell : ∀ x∈u::us,x.pre.wf=true := fun x hx => hwf _ (hmem x hx)
  have hdepth : ∀ x∈u::us, fdepth x.pre keyBwState≤400 := by
    intro x hx
    rcases List.mem_cons.mp (hmem x hx) with hx|hx
    · rw [hx,hm.pre]
      exact (built_spec w.main.values trieFuel k.slotB2.prevStateRoot _ hm.root_length).2.2.2 _
    · obtain ⟨e,he,hpre⟩ := List.mem_map.mp hx
      obtain ⟨hp,hr,_⟩ := hv.input_facts e he
      rw [←hpre,hp]
      exact (built_spec e.witness.values trieFuel e.root _ hr).2.2.2 _
  have hl := congrArg List.length hus
  simp only [List.length_map] at hl
  have hcount : (u::us).length≤32 := by simp only [List.length_cons]; omega
  have hout := schedulerUpserts_output_tight_charge (u::us) (fun x hx => (hvalid x hx).1) hwell
  rw [he] at hout
  have hb := checkD0a_preBytes hk hw h hm hv
  unfold B0 at hb
  have hval := scheduler_value_sum (u::us) (fun x hx => (hvalid x hx).2)
  refine ⟨u::us,he,by simp,hcount,?_,by simpa only [he] using hb,output_cost_arithmetic _ _ _ hb hcount hout,?_⟩
  · intro x hx
    have hp := traceUpsert_count x.pre keyBwState x.value x.run (hvalid x hx).1.1
    exact ⟨(hvalid x hx).1,hwell x hx,(by have hd := hdepth x hx; omega),hdepth x hx,(hvalid x hx).2⟩
  · omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
