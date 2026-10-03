import NearSpec.TransferV2
import NearSpec.TrieUpsertProofs

/-!
# Properties of the v2 bandwidth-scheduler step (proved)

`bandwidthStep_spec`: on a well-formed partial trie, the scheduler step writes
exactly one key — `0x0f` gets the new scheduler state, computed from the
previous state read from the same trie (absent ⇒ `State.initial`) — and every
other key (in particular every `Account` key the receipts touch afterwards)
looks up exactly as before, with proven absence and "unknown" preserved.

`bandwidthStep_value`: the written value in closed form — one link `(S, S)`
with allowance `4_400_000` if the link is allowed (`missed_chunks_count = 0`)
and `4_500_000` otherwise, and the chained sanity hash.
-/

namespace NearSpec.TransferV2

open NearSpec

theorem bwKeyPath_ok : nibblesOk bwKeyPath = true := by decide

theorem bandwidthStep_spec {ctx : Ctx} {t t' : PTrie} (hwf : t.wf = true)
    (h : bandwidthStep ctx t = some t') :
    ∃ st : Bandwidth.State,
      ((t.find bwKeyPath = some none ∧ st = Bandwidth.State.initial) ∨
        ∃ b, t.find bwKeyPath = some (some b) ∧ Bandwidth.State.decode b = some st) ∧
      t'.find bwKeyPath =
        some (some (Bandwidth.step ctx.shardId (Bandwidth.linkAllowed ctx.missedChunksCount) st).encode) ∧
      ∀ k, k ≠ bwKeyPath → t'.find k = t.find k := by
  unfold bandwidthStep at h
  cases hf : t.find bwKeyPath with
  | none => simp [hf] at h
  | some prev =>
    simp only [hf] at h
    cases prev with
    | none =>
      refine ⟨Bandwidth.State.initial, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
      · exact PTrie.find_upsert_self t _ _ t' bwKeyPath_ok h
      · intro k hk; exact PTrie.find_upsert_other t _ k _ t' hwf bwKeyPath_ok hk h
    | some b =>
      cases hd : Bandwidth.State.decode b with
      | none => simp [hd] at h
      | some st =>
        simp only [hd] at h
        refine ⟨st, Or.inr ⟨b, rfl, hd⟩, ?_, ?_⟩
        · exact PTrie.find_upsert_self t _ _ t' bwKeyPath_ok h
        · intro k hk; exact PTrie.find_upsert_other t _ k _ t' hwf bwKeyPath_ok hk h

theorem bandwidthStep_value (s m : Nat) (st : Bandwidth.State) :
    Bandwidth.step s (Bandwidth.linkAllowed m) st =
      { links := [⟨s, s, if m = 0 then 4400000 else 4500000⟩]
        sanityHash := sha256 (st.sanityHash ++ Bandwidth.allShardsHash s) } := by
  simp only [Bandwidth.step, Bandwidth.newAllowance_eq, Bandwidth.linkAllowed]
  cases m <;> simp

/-- The partial-trie computation of the scheduler write agrees with the same
computation on any more revealed trie (e.g. the full pre-state trie): equal
pre-roots and equal post-roots. -/
theorem bandwidthStep_refinedBy {ctx : Ctx} {t₁ t₂ t₁' : PTrie} (hr : t₁.refinedBy t₂)
    (h : bandwidthStep ctx t₁ = some t₁') :
    ∃ t₂', bandwidthStep ctx t₂ = some t₂' ∧ t₁'.hashOf = t₂'.hashOf := by
  unfold bandwidthStep at h ⊢
  cases hf : t₁.find bwKeyPath with
  | none => simp [hf] at h
  | some prev =>
    rw [PTrie.find_refinedBy t₁ t₂ _ prev hr hf]
    simp only [hf] at h ⊢
    cases prev with
    | none =>
      obtain ⟨-, t₂', h₂, he⟩ := PTrie.upsert_hashOf_congr hr h
      exact ⟨t₂', h₂, he⟩
    | some b =>
      cases hd : Bandwidth.State.decode b with
      | none => simp [hd] at h
      | some st =>
        simp only [hd] at h ⊢
        obtain ⟨-, t₂', h₂, he⟩ := PTrie.upsert_hashOf_congr hr h
        exact ⟨t₂', h₂, he⟩

end NearSpec.TransferV2
