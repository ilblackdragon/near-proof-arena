import ZkFormal.NearV3.Assembly.UpsertTightCost
import ZkFormal.NearV3.Assembly.NativeTrace
import ZkFormal.NearV3.Assembly.Scheduler

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Render.UpsGen

structure SchedulerUpsertWitness where
  ctx : ApplyCtx
  pre : PTrie
  value : Bytes
  run : TreeRun

def SchedulerUpsertWitness.Valid (u : SchedulerUpsertWitness) : Prop :=
  traceUpsert u.pre keyBwState u.value=some u.run ∧
  ∃ so, schedStep prims u.ctx u.pre=.ok (u.run.output,so) ∧ so.state=u.value

/-- Executable native scheduler trace extraction. -/
def schedulerUpsertWitness (ctx : ApplyCtx) (pre : PTrie) : Except String SchedulerUpsertWitness := do
  let (_,so) ← schedStep prims ctx pre
  match traceUpsert pre keyBwState so.state with
  | none => throw "scheduler upsert trace failed"
  | some run => pure ⟨ctx,pre,so.state,run⟩

theorem schedStep_upsert_witness {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (hs : schedStep prims ctx pre=.ok (post,so)) :
    ∃ u, schedulerUpsertWitness ctx pre=.ok u ∧ u.pre=pre ∧ u.Valid := by
  obtain ⟨_,_,_,_,_,_,_,hu⟩ := schedStep_complete hs
  obtain ⟨run,hr,he⟩ := traceUpsert_complete hu
  refine ⟨⟨ctx,pre,so.state,run⟩,?_,rfl,hr,so,?_,rfl⟩
  · simp [schedulerUpsertWitness,hs,hr,bind,Except.bind,pure,Except.pure]
  · simpa only [he] using hs

theorem applyNewChunk_upsert_witness {ctx : ApplyCtx} {pre : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx pre rs=.ok out) : ∃ u : SchedulerUpsertWitness, u.pre=pre ∧ u.Valid := by
  obtain ⟨mid,so,_,hs,_,_⟩ := Qv.applyNewChunk_queue_reads h
  obtain ⟨u,_,he,hv⟩ := schedStep_upsert_witness hs
  exact ⟨u,he,hv⟩

theorem applyMissingChunk_upsert_witness {ctx : ApplyCtx} {pre post : PTrie}
    (h : applyMissingChunk prims ctx pre=.ok post) : ∃ u : SchedulerUpsertWitness, u.pre=pre ∧ u.Valid := by
  unfold applyMissingChunk at h
  obtain ⟨_,_,h⟩ := ReexecV3D0.bind_ok' h
  obtain ⟨⟨mid,so⟩,hs,_⟩ := ReexecV3D0.bind_ok' h
  obtain ⟨u,_,he,hv⟩ := schedStep_upsert_witness hs
  exact ⟨u,he,hv⟩

theorem ImplicitTraceValid.upsert_witnesses {k root pairs steps last}
    (h : ImplicitTraceValid k root pairs steps last) :
    ∃ us : List SchedulerUpsertWitness,
      us.map SchedulerUpsertWitness.pre=steps.map ImplicitStepV3.pre ∧ ∀ u∈us,u.Valid := by
  induction h with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons root b t rest steps post last hr hp ht ih =>
    obtain ⟨u,he,hu⟩ := applyMissingChunk_upsert_witness hr
    obtain ⟨us,hes,hus⟩ := ih
    refine ⟨u::us,?_,?_⟩
    · simp [he,hes]
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl|hx
      exact hu
      exact hus x hx

/-- Fixed scheduler keys discharge the short-key condition. This does not
assert that arbitrary trie updates have short keys. -/
theorem SchedulerUpsertWitness.output_charge {u : SchedulerUpsertWitness}
    (hu : u.Valid) (hw : u.pre.wf=true) :
    outputByteCharge u.run≤4*unfoldedBytesT u.pre+4096 :=
  traceUpsert_output_charge_pre u.pre keyBwState u.value u.run hu.1 hw (by decide)

theorem schedulerUpserts_output_charge (us : List SchedulerUpsertWitness)
    (hv : ∀ u∈us,u.Valid) (hw : ∀ u∈us,u.pre.wf=true) :
    (us.map (fun u => outputByteCharge u.run)).sum≤
      4*preBytes (us.map SchedulerUpsertWitness.pre)+4096*us.length := by
  induction us with
  | nil => simp [preBytes]
  | cons u us ih =>
    have hh := SchedulerUpsertWitness.output_charge (hv u (by simp)) (hw u (by simp))
    have ht := ih (fun x hx => hv x (by simp [hx])) (fun x hx => hw x (by simp [hx]))
    simp only [preBytes,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    omega

private theorem output_cost_arithmetic (a b c : Nat) (hb : b≤2000000) (hc : c≤32)
    (ha : a≤4*b+4096*c) : a≤8131072 := by omega

/-- Actual accepted native execution yields every scheduler upsert, with a
single aggregate output-node byte charge derived from the unchanged A7 bound.
Fresh scheduler value bytes and other SHA kinds are not counted here. -/
theorem checkD0a_upsert_output_bytes {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ()) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀ u∈us,u.Valid ∧ u.pre.wf=true) ∧
      (us.map (fun u => outputByteCharge u.run)).sum≤8131072 := by
  obtain ⟨m,steps,last,hm,_,hv,_,hlen,_,hwf⟩ := checkD0a_native_trace hk hw h
  obtain ⟨u,hu,huv⟩ := applyNewChunk_upsert_witness hm.run
  obtain ⟨us,hus,husv⟩ := hv.upsert_witnesses
  have he : (u::us).map SchedulerUpsertWitness.pre=m.pre::steps.map ImplicitStepV3.pre := by
    simp [hu,hus]
  have hvalid : ∀ x∈u::us,x.Valid := by
    intro x hx; rcases List.mem_cons.mp hx with rfl|hx
    exact huv
    exact husv x hx
  have hwell : ∀ x∈u::us,x.pre.wf=true := by
    intro x hx
    apply hwf x.pre
    rw [←he]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hl := congrArg List.length hus
  simp only [List.length_map] at hl
  have hc := schedulerUpserts_output_charge (u::us) hvalid hwell
  rw [he] at hc
  have hb := checkD0a_preBytes hk hw h hm hv
  unfold B0 at hb
  refine ⟨u::us,by simp,?_,fun x hx => ⟨hvalid x hx,hwell x hx⟩,?_⟩
  · simp only [List.length_cons]; omega
  · exact output_cost_arithmetic _ _ _ hb (by simp only [List.length_cons]; omega) hc

theorem SchedulerUpsertWitness.output_tight_charge {u : SchedulerUpsertWitness}
    (hu : u.Valid) (hw : u.pre.wf=true) :
    outputByteCharge u.run≤unfoldedBytesT u.pre+4096 :=
  traceUpsert_output_node_charge_pre u.pre keyBwState u.value u.run hu.1 hw (by decide)

theorem schedulerUpserts_output_tight_charge (us : List SchedulerUpsertWitness)
    (hv : ∀ u∈us,u.Valid) (hw : ∀ u∈us,u.pre.wf=true) :
    (us.map (fun u => outputByteCharge u.run)).sum≤
      preBytes (us.map SchedulerUpsertWitness.pre)+4096*us.length := by
  induction us with
  | nil => simp [preBytes]
  | cons u us ih =>
    have hh := SchedulerUpsertWitness.output_tight_charge (hv u (by simp)) (hw u (by simp))
    have ht := ih (fun x hx => hv x (by simp [hx])) (fun x hx => hw x (by simp [hx]))
    simp only [preBytes,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    omega

private theorem output_tight_arithmetic (a b c : Nat) (hb : b≤2000000) (hc : c≤32)
    (ha : a≤b+4096*c) : a≤2131072 := by omega

/-- Actual accepted native execution yields every scheduler upsert, with a
single aggregate output-node byte charge derived from the unchanged A7 bound.
Fresh scheduler value bytes and other SHA kinds are not counted here. -/
theorem checkD0a_upsert_output_bytes_tight {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ()) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧ (∀ u∈us,u.Valid ∧ u.pre.wf=true) ∧
      (us.map (fun u => outputByteCharge u.run)).sum≤2131072 := by
  obtain ⟨m,steps,last,hm,_,hv,_,hlen,_,hwf⟩ := checkD0a_native_trace hk hw h
  obtain ⟨u,hu,huv⟩ := applyNewChunk_upsert_witness hm.run
  obtain ⟨us,hus,husv⟩ := hv.upsert_witnesses
  have he : (u::us).map SchedulerUpsertWitness.pre=m.pre::steps.map ImplicitStepV3.pre := by
    simp [hu,hus]
  have hvalid : ∀ x∈u::us,x.Valid := by
    intro x hx; rcases List.mem_cons.mp hx with rfl|hx
    exact huv
    exact husv x hx
  have hwell : ∀ x∈u::us,x.pre.wf=true := by
    intro x hx
    apply hwf x.pre
    rw [←he]
    exact List.mem_map.mpr ⟨x,hx,rfl⟩
  have hl := congrArg List.length hus
  simp only [List.length_map] at hl
  have hc := schedulerUpserts_output_tight_charge (u::us) hvalid hwell
  rw [he] at hc
  have hb := checkD0a_preBytes hk hw h hm hv
  unfold B0 at hb
  refine ⟨u::us,by simp,?_,fun x hx => ⟨hvalid x hx,hwell x hx⟩,?_⟩
  · simp only [List.length_cons]; omega
  · exact output_tight_arithmetic _ _ _ hb (by simp only [List.length_cons]; omega) hc

end ZkFormal.NearV3.Assembly
