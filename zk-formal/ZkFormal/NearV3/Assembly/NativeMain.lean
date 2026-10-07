import ZkFormal.NearV3.Assembly.SourceResult
import ZkFormal.NearV3.Assembly.Execution
import ZkFormal.NearV3.Assembly.RuntimeReplay

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem mapError_id {α : Type} (x : Except String α) : x.mapError id = x := by
  cases x <;> rfl

structure MainExecutionV3.NativeValid (k : WalkD0) (w : StateWitness)
    (m : MainExecutionV3) : Prop where
  block : k.blks[k.b2i]? = some m.block
  previous : k.blks[k.b2i + 1]? = some m.previous
  buffered : ∃ v, (partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]).find
    keyBufferedIdx = some v ∧ NearSpecV3.bufferedShards v = .ok m.bufferedShards
  pre : m.pre = partialTrie w.main.values k.slotB2.prevStateRoot
    (mainKeys (appliedReceipts k w) m.bufferedShards)
  preRoot : m.pre.hashOf = k.slotB2.prevStateRoot
  run : applyNewChunk prims (m.ctx k) m.pre (appliedReceipts k w) = .ok m.result
  postRoot : m.result.trie.hashOf = w.main.postStateRoot

set_option maxHeartbeats 4000000 in
theorem checkD0_native_main {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0 cb wb = .ok ()) :
    ∃ m : MainExecutionV3, m.NativeValid k w := by
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
      have hv := checkedSourceLoop_result _ _ _ _ (by assumption)
      -- Name the values returned by the frozen checker binds; congruence aligns
      -- its walk indices with the independently decoded WalkD0.
      expose_names
      have hb2 : w_6 = w_36 := by grind only
      have hslot : w_8 = w_44 := by
        rw [hb2, heq_5] at heq_3
        simp only [Option.bind_some, heq_8, Option.some.injEq] at heq_3
        grind only
      refine ⟨⟨w_37, w_43, w_52,
        partialTrie w_13.main.values w_44.prevStateRoot (mainKeys w_45.1 w_52), w_54⟩, ?_⟩
      constructor
      · grind only
      · grind only
      · refine ⟨v, ?_, ?_⟩
        · grind only
        · have hh : (bufferedShards v).mapError id = .ok w_52 := by assumption
          simpa only [mapError_id] using hh
      · simp only [appliedReceipts_eq_flatMap]
        grind only
      · grind only [check_ok]
      · simp only [MainExecutionV3.ctx, appliedReceipts_eq_flatMap]
        grind only
      · grind only [check_ok]

/-- Populate the semantic main-execution interface from actual native execution
and the concrete normalized store emitted by the allocated views. -/
theorem MainExecutionV3.NativeValid.normalized {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {x : ExtV3} (h : m.NativeValid k w)
    (hr : k.slotB2.prevStateRoot.length = 32)
    (hs : x.store 0 = normalStore m.pre)
    (ha : x.applied = appliedReceipts k w)
    (hp : x.post 0 = w.main.postStateRoot) : m.Valid k x := by
  have hrun := h.run
  rw [h.pre] at hrun
  have hbuf := applyNewChunk_normalStore_buffered hr hrun
  constructor
  · exact h.block
  · exact h.previous
  · obtain ⟨v, hv, hh⟩ := h.buffered
    refine ⟨v, ?_, hh⟩
    rw [hs, h.pre, hbuf]
    exact hv
  · rw [hs, ha, h.pre, partialTrie_normalStore _ _ _ hr]
  · exact h.preRoot
  · rw [ha]
    exact h.run
  · rw [hp]
    exact h.postRoot

end ZkFormal.NearV3.Assembly
