import ZkFormal.NearV3.Sched.Pub.Prep

/-!
# ZkFormal.NearV3.Sched.Link.SoundPrep — one layout for every scheduler instance (`prepD0`)

`render` sends the `SDL` id records of instance 0's layout only (`dlRecs 0 (Ps[0]).ids`), and the
codec passes them from instance to instance. The instances agree on the layout because `prepClaim`
builds every apply context with the one layout `L` of the claim:

* **`prepD0_ids`**: `prepD0 cb h = .ok p → ∃ ids, ∀ sp ∈ p.sched, sp.ids = ids`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

theorem schedPub_ids {ctx : ApplyCtx} {sp : SchedPub} (h : schedPub ctx = some sp) :
    sp.ids = ctx.layout.shardIds := by
  unfold schedPub pubOf at h
  by_cases hn : ctx.layout.shardIds.length = 0
  · simp [hn] at h
  · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
    | none => simp [hn, hp] at h
    | some p =>
      simp only [hn, hp, ↓reduceIte] at h
      simp only [Option.bind, bind, Option.some.injEq] at h
      subst h; rfl

/-- The closing step of `prepClaim` for the layout. -/
theorem ids_close {L : Layout} {own g gp : Nat} {B2 : Blk} {xs : List Blk} {sched : List SchedPub}
    {f : ApplyCtx → Except String SchedPub}
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M => blockCtx L own g M M.hdr.nextGasPrice) xs) = .ok sched)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) :
    ∀ sp ∈ sched, sp.ids = L.shardIds := by
  intro sp hsp
  obtain ⟨ctx, hctx, hfc⟩ := mapM_ok f _ _ hm sp hsp
  rw [schedPub_ids (hf ctx sp hfc)]
  rcases List.mem_cons.1 hctx with e | e
  · subst e; rfl
  · obtain ⟨M, -, rfl⟩ := List.mem_map.1 e; rfl

set_option maxHeartbeats 4000000 in
theorem prepClaim_ids {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∃ ids, ∀ sp ∈ pc.sched, sp.ids = ids := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨_, ids_close (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)⟩

/-- **One layout for every scheduler instance of a successful `prepD0`.** -/
theorem prepD0_ids {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∃ ids, ∀ sp ∈ p.sched, sp.ids = ids := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_ids hpc

end ZkFormal.NearV3.Sched
