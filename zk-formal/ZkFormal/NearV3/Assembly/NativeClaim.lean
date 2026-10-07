import ZkFormal.NearV3.Assembly.ClaimFacts
import ZkFormal.NearV3.Assembly.NativeMain

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

set_option maxHeartbeats 4000000 in
theorem checkD0_claim_guards {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ClaimGuardsV3 k ∧ k.slotB2.txRoot = zeroHash32 ∧
      (k.slotB2.congestion.delayedGas == 0 && k.slotB2.congestion.bufferedGas == 0 &&
        k.slotB2.congestion.receiptBytes == 0) = true := by
  unfold walkD0 at hk
  repeat' (first
    | (have hh := hk; clear hk; obtain ⟨_, _, hk⟩ := bind_ok hh; clear hh)
    | (split at hk)
    | (dsimp only at hk))
  all_goals try (cases hk; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at hk
    subst hk
    unfold decodeW at hw
    obtain ⟨⟨raw, codes⟩, hfile, hw⟩ := bind_ok hw
    unfold checkD0 at h
    repeat' (first
      | (have hh := h; clear h; obtain ⟨_, _, h⟩ := bind_ok hh; clear hh)
      | (split at h)
      | (dsimp only at h))
    all_goals try (cases h; done)
    all_goals try (exfalso; exact throw_ne (by assumption))
    all_goals
      simp_all only [Except.mapError, Except.ok.injEq, Prod.mk.injEq, pure, Except.pure, Option.some.injEq]
      expose_names
      have hb2 : w_6 = w_36 := by grind only
      have hslot : w_8 = w_44 := by
        rw [hb2, heq_5] at heq_3
        simp only [Option.bind_some, heq_8, Option.some.injEq] at heq_3
        grind only
      refine ⟨?_,?_,?_⟩
      · constructor <;> grind only [check_ok]
      · grind only [check_ok]
      · grind only [check_ok]

end ZkFormal.NearV3.Assembly
