import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched Rcpt.Candidates

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_source_lists {cb : Bytes} {pc : PrepC} {k : WalkD0}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) : preparedSourceLists k.sourceBlks = .ok pc.lists := by
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
      unfold preparedSourceLists slotSources
      simp_all only [pure, Except.pure, bind, Except.bind]
      grind only

theorem prepD0_source_lists {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint = .ok p) (hw : walkD0 cb = .ok k) :
    preparedSourceLists k.sourceBlks = .ok p.lists := by
  obtain ⟨pc, hc, hb⟩ := bind_ok hp
  rw [(prepBody_shape hb).2.2.1]
  exact prepClaim_source_lists hc hw

end ZkFormal.NearV3.Assembly
