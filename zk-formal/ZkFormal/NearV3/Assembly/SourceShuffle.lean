import ZkFormal.NearV3.Assembly.SourceComplete

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem checkedSourceBlock_trace (entries : List ProofEntry) (own : Nat) (L : Layout)
    (b : Blk) (acc : List Receipt × Nat) {step : ForInStep (List Receipt × Nat)}
    (h : checkedSourceBlock entries own L b acc = .ok step) :
    (∃ next, step = .yield next) ∧
      ((∀ x ∈ b.slots, SourceSlotValid entries own b x) →
        ∃ shuffled, shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled) := by
  unfold checkedSourceBlock at h
  obtain ⟨out, ho, h⟩ := bind_ok h
  split at h
  · rename_i shuffled hs
    obtain ⟨_, he, h⟩ := bind_ok h
    cases he
    cases h
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro hv
    have hh := checkedSourceSlots_complete entries own b b.slots hv acc.2 []
    rw [ho] at hh
    have hl := congrArg Prod.snd (Except.ok.inj hh)
    refine ⟨shuffled, ?_⟩
    simpa only [hl, List.nil_append] using hs
  · obtain ⟨_, he, _⟩ := bind_ok h
    cases he

theorem checkedSourceLoop_shuffle (entries : List ProofEntry) (own : Nat) (L : Layout)
    (blocks : List Blk) {out : List Receipt × Nat}
    (h : forIn blocks ([], 0) (checkedSourceBlock entries own L) = .ok out) :
    ∀ b ∈ blocks, ∃ shuffled,
      shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled := by
  have hv := checkedSourceLoop_valid entries own L blocks h
  have hs := forIn_all_yield _ _ (checkedSourceBlock_trace entries own L) blocks ([], 0) out h
  exact fun b hb => hs b hb (hv b hb)

set_option maxHeartbeats 4000000 in
/-- Every actual selected-source shuffle succeeds in an accepted native check. -/
theorem checkD0_sources_shuffle {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ∀ b ∈ k.sourceBlks, ∃ shuffled,
      shuffleWithSeed (selectedEntries w.entries b b.slots) b.hdr.prevHash = some shuffled := by
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
      have hv := checkedSourceLoop_shuffle _ _ _ _ (by assumption)
      grind only


end ZkFormal.NearV3.Assembly
