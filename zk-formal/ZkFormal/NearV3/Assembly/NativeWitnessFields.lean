import ZkFormal.NearV3.Assembly.SourceResult

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched
set_option maxHeartbeats 4000000 in
/-- Actual accepted witness envelope and fields used by canonical reconstruction. -/
theorem checkD0_witness_fields {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ∃ raw codes, decodeWitnessFile wb = .ok (raw,codes) ∧ decodeStateWitness raw = .ok w ∧
      raw.length ≤ 8388608 ∧ w.epochId = k.c.epochId ∧ w.innerBytes = k.c.chunkInner ∧
      sha256 (encodeReceipts (appliedReceipts k w)) = w.appliedReceiptsHash := by
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
      refine ⟨raw,codes,hfile,hw,?_⟩
      simp_all only [Except.mapError, Except.ok.injEq, Prod.mk.injEq, pure, Except.pure, Option.some.injEq]
      have hv := checkedSourceLoop_result _ _ _ _ (by assumption)
      refine ⟨?_,?_,?_,?_⟩
      all_goals try simp only [appliedReceipts_eq_flatMap]
      all_goals grind only [check_ok, ReexecV3D0.lenT_eq]

end ZkFormal.NearV3.Assembly
