import ZkFormal.NearV3.Assembly.NativeMain

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

structure NativePrepContext (k : WalkD0) (m : MainExecutionV3) (pc : PrepC) : Prop where
  ctx : pc.ctxB2 = m.ctx k
  header : pc.H = k.H
  layout : pc.L = k.L
  gasLimit : pc.hdr.gasLimit = k.slotB2.gasLimit
  congestion : pc.ownCongestion = k.slotB2.congestion
  allowed : pc.allowed = k.L.shardIds.getD ((m.block.hdr.height + k.idx) % k.L.numShards) k.H.shardId
  rsData : pc.rsData = k.c.rsDataParts
  rsTotal : pc.rsTotal = k.c.rsTotalParts

private theorem mapError_ok_iff {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

set_option maxHeartbeats 4000000 in
theorem prepClaim_native_context {cb : Bytes} {pc : PrepC} {k : WalkD0}
    {w : StateWitness} {m : MainExecutionV3}
    (hp : prepClaim cb = .ok pc) (hw : walkD0 cb = .ok k) (hm : m.NativeValid k w) :
    NativePrepContext k m pc := by
  have hmb := hm.block
  have hmp := hm.previous
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
      expose_names
      have hb2 : w_23 = i_3 := by grind only
      have hslot : p_1.2 = w_31 := by
        rw [←hb2,heq_2] at heq_8
        simp only [Option.bind_some,heq_5,Option.some.injEq] at heq_8
        grind only
      constructor <;> dsimp only [MainExecutionV3.ctx] <;> grind only

end ZkFormal.NearV3.Assembly
