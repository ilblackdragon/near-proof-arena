import ZkFormal.NearV3.Sched.Pub.Prep

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem schedPub_exists (ctx : ApplyCtx) (hn : 0 < ctx.layout.numShards) :
    ∃ p, schedPub ctx = some p := by
  have hn' : ctx.layout.shardIds.length ≠ 0 := Nat.ne_of_gt hn
  simp only [schedPub, Scheduler.pubOf, hn', ↓reduceIte,
    Scheduler.Params.calculate, Scheduler.Config.pv86]
  simp

theorem schedPub_mapM_exists (ctxs : List ApplyCtx)
    (hn : ∀ ctx ∈ ctxs, 0 < ctx.layout.numShards) :
    ∃ ps, ctxs.mapM (fun ctx => match schedPub ctx with
      | some p => pure p
      | none => throw "invalid: bandwidth scheduler aborted (StorageInconsistentState)") =
        (Except.ok ps : Except String (List Scheduler.SchedPub)) := by
  induction ctxs with
  | nil => exact ⟨[],rfl⟩
  | cons ctx ctxs ih =>
    obtain ⟨p,hp⟩ := schedPub_exists ctx (hn ctx (by simp))
    obtain ⟨ps,hps⟩ := ih (fun c hc => hn c (List.mem_cons_of_mem _ hc))
    simp only [pure,Except.pure] at hps
    refine ⟨p::ps,?_⟩
    simp only [List.mapM_cons,hp,hps,pure,Except.pure,bind,Except.bind]

end ZkFormal.NearV3.Assembly
