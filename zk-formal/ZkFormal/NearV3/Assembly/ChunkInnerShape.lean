import ZkFormal.NearV3.Assembly.RawHeaderShape

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pOption_property {α : Type} (p : P α) (q : α → Bool)
    (hq : ∀ bs a rest, p bs = .ok (a,rest) → q a = true)
    {label : String} {bs rest : Bytes} {a : Option α}
    (h : pOption label p bs = .ok (a,rest)) :
    (match a with | none => true | some v => q v) = true := by
  unfold pOption at h
  obtain ⟨⟨tag,r⟩,_,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h; rfl
  · obtain ⟨⟨v,r'⟩,hv,h⟩ := bind_ok h
    cases h
    exact hq _ _ _ hv
  · cases h

set_option maxHeartbeats 2000000 in
theorem pChunkInner_shape {bs rest : Bytes} {ci : ChunkInner}
    (h : pChunkInner bs = .ok (ci,rest)) : V3.innerWf ci = true := by
  unfold pChunkInner at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_,_,h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    have hprops := pVec_property pValidatorStake (fun v => V3.vsWf v = true)
      (fun _ _ _ hh => pValidatorStake_shape hh) (by assumption)
    have hbw := pBwRequests_shape (by assumption)
    try (have hop := pOption_property pTrieSplit V3.tsWf (fun _ _ _ hh => pTrieSplit_shape hh) (by assumption))
    try simp_all only [pure,Except.pure,Except.ok.injEq]
    subst_vars
    simp only [V3.innerWf,V3.h32,Option.isNone,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
    repeat' apply And.intro
    all_goals first
      | exact V3.pHash_len (by assumption)
      | exact V3.pU128_lt (by assumption)
      | exact (ReexecV3D0.lift_readLE_inv (n := 8) (by assumption)).2
      | exact pVec_length_bound (by assumption)
      | exact List.all_eq_true.mpr hprops
      | exact pCongestion_shape (by assumption)
      | exact hbw.1
      | exact hbw.2
      | exact pOption_property pTrieSplit V3.tsWf (fun _ _ _ hh => pTrieSplit_shape hh) (by assumption)
      | grind only

end ZkFormal.NearV3.Assembly
