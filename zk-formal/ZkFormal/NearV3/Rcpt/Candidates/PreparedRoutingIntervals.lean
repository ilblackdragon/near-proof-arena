import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched Rcpt.Candidates

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_routing_intervals {cb : Bytes} {pc : PrepC} {k : WalkD0}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) : pc.bnds=ownIntervals k.L k.H.shardId := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    simp_all only [mapError_ok_iff, pure, Except.pure, Except.ok.injEq]
    unfold walkD0 at hw
    simp only [*, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hw
    repeat' (first
      | (have hh := hw; clear hw; obtain ⟨_, _, hw⟩ := bind_ok hh; clear hh)
      | (split at hw)
      | (dsimp only at hw))
    all_goals try (cases hw; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp only [pure, Except.pure, Except.ok.injEq] at hw
      subst hw
      simp_all only [pure, Except.pure, bind, Except.bind]

theorem prepBody_routing_intervals {pc : PrepC} {hint : Hint} {p : Prep}
    (h : prepBody pc hint=.ok p) : p.bnds=pc.bnds := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure,Except.pure,Except.ok.injEq] at h; subst h; rfl)
    | (exfalso; exact throw_ne (by assumption))

theorem prepD0_routing_intervals {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) : p.bnds=ownIntervals k.L k.H.shardId := by
  obtain ⟨pc,hc,hb⟩ := bind_ok hp
  exact (prepBody_routing_intervals hb).trans (prepClaim_routing_intervals hc hw)

end ZkFormal.NearV3.Assembly
