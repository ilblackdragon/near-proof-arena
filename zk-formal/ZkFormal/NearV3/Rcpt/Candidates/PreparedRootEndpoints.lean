import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched Rcpt.Candidates

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_root_endpoints {cb : Bytes} {pc : PrepC} {k : WalkD0}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) : pc.hdr.prevStateRoot=k.slotB2.prevStateRoot ∧ pc.hdr.postStateRoot=k.H.prevStateRoot ∧ pc.hdr.K=k.implicitBlks.length := by
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
      expose_names
      have hi : w_22=i_3 := by
        have hh : List.findIdx? (fun b => match b.slots[w_20]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_13=some w_22 := heq_1
        have hh' : List.findIdx? (fun b => match b.slots[w_20]? with
          | some (s,_) => s.heightIncluded == b.hdr.height
          | none => false) w_13=some i_3 := heq_6
        exact Option.some.inj (hh.symm.trans hh')
      have hs : w_30=p_1.2 := by
        rw [←hi,heq_2] at heq_8
        simp only [Option.bind_some,heq_5,Option.some.injEq] at heq_8
        grind only
      exact ⟨congrArg ChunkInner.prevStateRoot hs,True.intro,by rw [hi]⟩


theorem prepD0_root_endpoints {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint=.ok p) (hw : walkD0 cb=.ok k) :
    p.hdr.prevStateRoot=k.slotB2.prevStateRoot ∧ p.hdr.postStateRoot=k.H.prevStateRoot ∧
      p.hdr.K=k.implicitBlks.length := by
  obtain ⟨pc,hc,hb⟩:=bind_ok hp
  rw [(prepBody_shape hb).1,(prepBody_shape hb).2.2.2.1,(prepBody_shape hb).2.2.2.2.1]
  exact prepClaim_root_endpoints hc hw

end ZkFormal.NearV3.Assembly
