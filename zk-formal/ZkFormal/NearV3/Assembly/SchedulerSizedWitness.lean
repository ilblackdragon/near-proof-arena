import ZkFormal.NearV3.Assembly.SchedulerStateSize
import ZkFormal.NearV3.Assembly.NativeClaim

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

theorem schedulerUpsertWitness_ctx {ctx : ApplyCtx} {pre : PTrie} {u : SchedulerUpsertWitness}
    (h : schedulerUpsertWitness ctx pre=.ok u) : u.ctx=ctx := by
  unfold schedulerUpsertWitness at h
  obtain ⟨⟨post,so⟩,_,h⟩ := ReexecV3D0.bind_ok' h
  dsimp only at h
  cases ht : traceUpsert pre keyBwState so.state with
  | none => simp [ht] at h
  | some run => simp [ht,pure,Except.pure,Except.ok.injEq] at h; subst u; rfl

theorem schedStep_sized_witness {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hs : schedStep prims ctx pre=.ok (post,so)) (hl : ctx.layout.numShards≤64) :
    ∃ u : SchedulerUpsertWitness, u.pre=pre ∧ u.Valid ∧ u.value.length≤98341 := by
  obtain ⟨u,he,hp,hv⟩ := schedStep_upsert_witness hs
  have hc := schedulerUpsertWitness_ctx he
  exact ⟨u,hp,hv,SchedulerUpsertWitness.value_bound hv (by rw [hc]; exact hl)⟩

theorem applyNewChunk_sized_witness {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx pre rs=.ok out) (hl : ctx.layout.numShards≤64) :
    ∃ u : SchedulerUpsertWitness,u.pre=pre ∧ u.Valid ∧ u.value.length≤98341 := by
  obtain ⟨_,_,_,hs,_,_⟩ := Qv.applyNewChunk_queue_reads h
  exact schedStep_sized_witness hs hl

theorem applyMissingChunk_sized_witness {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre=.ok post) (hl : ctx.layout.numShards≤64) :
    ∃ u : SchedulerUpsertWitness,u.pre=pre ∧ u.Valid ∧ u.value.length≤98341 := by
  unfold applyMissingChunk at h
  obtain ⟨_,_,h⟩ := ReexecV3D0.bind_ok' h
  obtain ⟨⟨mid,so⟩,hs,_⟩ := ReexecV3D0.bind_ok' h
  exact schedStep_sized_witness hs hl

theorem ImplicitTraceValid.sized_upserts {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) (hl : k.L.numShards≤64) :
    ∃ us : List SchedulerUpsertWitness,
      us.map SchedulerUpsertWitness.pre=steps.map ImplicitStepV3.pre ∧
      ∀ u∈us,u.Valid ∧ u.value.length≤98341 := by
  induction h with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons root b t rest steps post last hr hp ht ih =>
    obtain ⟨u,he,hu⟩ := applyMissingChunk_sized_witness hr hl
    obtain ⟨us,hes,hus⟩ := ih
    refine ⟨u::us,?_,?_⟩
    · simp [he,hes]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      exact hu
      exact hus x hx

theorem scheduler_value_sum (us : List SchedulerUpsertWitness)
    (hv : ∀ u∈us,u.value.length≤98341) :
    (us.map (fun u => u.value.length)).sum≤98341*us.length := by
  induction us with
  | nil => simp
  | cons u us ih =>
    have hh := hv u (by simp)
    have ht := ih (fun x hx => hv x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem output_cost_arithmetic (a b c : Nat) (hb : b≤2000000) (hc : c≤32)
    (ha : a≤b+4096*c) : a≤2131072 := by omega

/-- Both fresh value bytes and all output-node bytes are charged for the actual
accepted scheduler executions. Static value size does not assume value changes. -/
theorem checkD0a_upsert_byte_budget {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ()) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧
      (∀ u∈us,u.Valid ∧ u.pre.wf=true ∧ u.run.parts.length≤403) ∧
      (us.map (fun u => outputByteCharge u.run)).sum≤2131072 ∧
      (us.map (fun u => u.value.length)).sum≤3146912 := by
  have hc : checkD0 cb wb=.ok () := by
    unfold checkD0a at h
    obtain ⟨u,hu,_⟩ := ReexecV3D0.bind_ok' h
    cases u; exact hu
  have hL := (checkD0_claim_guards hk hw hc).1.layout.2
  obtain ⟨m,steps,last,hm,_,hv,_,hlen,_,hwf⟩ := checkD0a_native_trace hk hw h
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
  refine ⟨u::us,by simp,hcount,?_,output_cost_arithmetic _ _ _ hb hcount hout,?_⟩
  · intro x hx
    have hp := traceUpsert_count x.pre keyBwState x.value x.run (hvalid x hx).1.1
    exact ⟨(hvalid x hx).1,hwell x hx,by have hd := hdepth x hx; omega⟩
  · omega

end ZkFormal.NearV3.Assembly
