import NearSpecV3.PrepD0

/-!
Runtime/preprocessing factorization for the bandwidth scheduler. These lemmas
extract the native public input and the state-dependent execution from actual
successful trie execution; neither success is an extra premise. This is one
component of whole-checker FactorComplete, not the complete assembly theorem.
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The runtime's projection of the scheduler's full output. -/
def schedOut (o : Scheduler.Output) : SchedOut :=
  ⟨o.state, fun a b => ((o.granted.find? (·.1 == (a, b))).map (·.2)).getD 0⟩

/-- The runtime call uses exactly preprocessing's public input and core. -/
theorem sched_factor (ctx : ApplyCtx) (prev : Option Bytes) :
    prims.sched ⟨ctx.layout.shardIds, ctx.own, prev, ctx.statuses, ctx.requests,
      ctx.prevBlockHash⟩ =
      (schedPub ctx).bind (fun p => (Scheduler.runCore p prev).map schedOut) := by
  simp only [prims, Scheduler.run_eq_core, schedPub]
  cases Scheduler.pubOf Scheduler.Config.pv86 CongestionConfig.pv86 ctx.layout.shardIds
      (ctx.statuses.map fun (s, c, m) => (s, toCI c, m))
      (ctx.requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
      ctx.prevBlockHash <;> rfl

/-- Successful trie execution supplies all scheduler witness data and proves
that the claim-only preprocessing call succeeds on this context. -/
theorem schedStep_complete {ctx : ApplyCtx} {t t' : PTrie} {so : SchedOut}
    (h : schedStep prims ctx t = .ok (t', so)) :
    ∃ prev p o, readKey t keyBwState "bandwidth scheduler state" = .ok prev ∧
      schedPub ctx = some p ∧ Scheduler.runCore p prev = some o ∧
      schedOut o = so ∧ t.upsert keyBwState so.state = some t' := by
  unfold schedStep at h
  obtain ⟨prev, hr, h⟩ := bind_ok h
  rw [sched_factor] at h
  cases hp : schedPub ctx with
  | none => simp [hp, bind, Except.bind] at h
  | some p =>
    cases ho : Scheduler.runCore p prev with
    | none => simp [hp, ho, bind, Except.bind] at h
    | some o =>
      simp only [hp, ho, Option.bind_some, Option.map_some, pure, Except.pure,
        bind, Except.bind] at h
      cases ht : t.upsert keyBwState (schedOut o).state with
      | none => simp [ht] at h
      | some u =>
        simp only [ht, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨prev, p, o, hr, rfl, ho, rfl, ht⟩

/-- Recombine the public preprocessing result and witnessed core execution into
the actual runtime trie step, including the read and write checks. -/
theorem schedStep_sound {ctx : ApplyCtx} {t t' : PTrie} {prev : Option Bytes}
    {p : Scheduler.SchedPub} {o : Scheduler.Output}
    (hr : readKey t keyBwState "bandwidth scheduler state" = .ok prev)
    (hp : schedPub ctx = some p) (ho : Scheduler.runCore p prev = some o)
    (ht : t.upsert keyBwState (schedOut o).state = some t') :
    schedStep prims ctx t = .ok (t', schedOut o) := by
  unfold schedStep
  rw [hr]
  simp only [bind, Except.bind]
  rw [sched_factor, hp, Option.bind_some, ho, Option.map_some]
  simp only [pure, Except.pure, ht]

/-- Exact scheduler factorization, usable in both assembly directions. -/
theorem schedStep_iff {ctx : ApplyCtx} {t t' : PTrie} {so : SchedOut} :
    schedStep prims ctx t = .ok (t', so) ↔
    ∃ prev p o, readKey t keyBwState "bandwidth scheduler state" = .ok prev ∧
      schedPub ctx = some p ∧ Scheduler.runCore p prev = some o ∧
      schedOut o = so ∧ t.upsert keyBwState so.state = some t' := by
  constructor
  · exact schedStep_complete
  · rintro ⟨prev, p, o, hr, hp, ho, rfl, ht⟩
    exact schedStep_sound hr hp ho ht

/-- Main application cannot succeed unless native scheduler preprocessing does. -/
theorem applyNewChunk_schedPub {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt}
    {out : MainOut} (h : applyNewChunk prims ctx t rs = .ok out) :
    ∃ p, schedPub ctx = some p := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨t', so⟩, hs, _⟩ := bind_ok h
  obtain ⟨_, p, _, _, hp, _⟩ := schedStep_complete hs
  exact ⟨p, hp⟩

/-- The same obligation for every implicit (missing-chunk) transition. -/
theorem applyMissingChunk_schedPub {ctx : ApplyCtx} {t t' : PTrie}
    (h : applyMissingChunk prims ctx t = .ok t') : ∃ p, schedPub ctx = some p := by
  unfold applyMissingChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨u, so⟩, hs, _⟩ := bind_ok h
  obtain ⟨_, p, _, _, hp, _⟩ := schedStep_complete hs
  exact ⟨p, hp⟩

end ZkFormal.NearV3.Assembly
