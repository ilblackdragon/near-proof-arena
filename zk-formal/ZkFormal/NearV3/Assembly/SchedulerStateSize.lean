import ZkFormal.NearV3.Assembly.SchedulerUpsertCost

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

theorem scheduler_links_encoded_length (xs : List Bandwidth.LinkAllowance) :
    (concatAll (xs.map Bandwidth.LinkAllowance.encode)).length=24*xs.length := by
  induction xs with
  | nil => simp [concatAll]
  | cons x xs ih => simp [concatAll,Bandwidth.LinkAllowance.encode] at ih ⊢; omega

theorem scheduler_state_encoded_length (s : Bandwidth.State) :
    s.encode.length=5+24*s.links.length+s.sanityHash.length := by
  simp [Bandwidth.State.encode,scheduler_links_encoded_length]
  omega

/-- Native core always emits one24-byte link per ordered pair, plus tag/count
and the actual32-byte sanity hash. No assumption on prior state's link count. -/
theorem scheduler_core_state_length {pub : Scheduler.SchedPub} {prev : Option Bytes} {out : Scheduler.Output}
    (h : Scheduler.runCore pub prev=some out) :
    out.state.length=37+24*(pub.ids.length*pub.ids.length) := by
  unfold Scheduler.runCore at h
  cases prev <;> dsimp only at h
  all_goals
    obtain ⟨old,_,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨st,_,h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst out
    simp [scheduler_state_encoded_length]
    omega

/-- Claim-only scheduling preserves the context's exact shard list. -/
theorem schedPub_ids {ctx : ApplyCtx} {pub : Scheduler.SchedPub} (h : schedPub ctx=some pub) :
    pub.ids=ctx.layout.shardIds := by
  unfold schedPub Scheduler.pubOf at h
  dsimp only at h
  split at h
  · simp [bind,Option.bind] at h
  · obtain ⟨p,_,h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rfl

theorem schedStep_state_length {ctx : ApplyCtx} {pre post : PTrie} {so : SchedOut}
    (h : schedStep prims ctx pre=.ok (post,so)) :
    so.state.length=37+24*(ctx.layout.numShards*ctx.layout.numShards) := by
  obtain ⟨prev,p,o,_,hp,ho,he,_⟩ := schedStep_complete h
  have hs := scheduler_core_state_length ho
  rw [schedPub_ids hp] at hs
  rw [←he]
  exact hs

theorem SchedulerUpsertWitness.value_length {u : SchedulerUpsertWitness} (h : u.Valid) :
    u.value.length=37+24*(u.ctx.layout.numShards*u.ctx.layout.numShards) := by
  obtain ⟨so,hs,he⟩ := h.2
  rw [←he]
  exact schedStep_state_length hs

theorem SchedulerUpsertWitness.value_bound {u : SchedulerUpsertWitness} (h : u.Valid)
    (hl : u.ctx.layout.numShards≤64) : u.value.length≤98341 := by
  rw [SchedulerUpsertWitness.value_length h]
  have hh := Nat.mul_self_le_mul_self hl
  omega

end ZkFormal.NearV3.Assembly
