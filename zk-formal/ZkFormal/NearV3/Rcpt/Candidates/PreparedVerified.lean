import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount
import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition
import ZkFormal.NearV3.Rcpt.Link.SourceLoop

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

private theorem forIn_invariant {α β : Type} (Q : β → Prop)
    (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α) (start out : β), Q start →
      (∀ a ∈ xs, ∀ b, Q b → ∀ step, f a b = .ok step →
        match step with | .done v => Q v | .yield v => Q v) →
      forIn xs start f = .ok out → Q out
  | [], start, out, hq, _, h => by cases h; exact hq
  | a :: xs, start, out, hq, hs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hf, h⟩ := bind_ok h
    have hp := hs a (by simp) start hq step hf
    cases step with
    | done v => cases h; exact hp
    | yield v =>
      exact forIn_invariant Q f xs v out hp
        (fun x hx => hs x (by simp [hx])) h

def PreparedSourceVerified (entries : List ProofEntry) (s : SrcList) : Prop :=
  ∃ e, lookupLast s.key entries = some e ∧ verifyReceiptProof s.root e = true

/-- The actual claim-side slot renderer preserves authenticated source descriptors. -/
theorem slotSources_verified (entries : List ProofEntry) (own : Nat) (B : Blk)
    (hv : ∀ x ∈ B.slots, SourceSlotValid entries own B x)
    {out : List SrcList} (h : slotSources B = .ok out) :
    ∀ s ∈ out, PreparedSourceVerified entries s := by
  apply forIn_invariant (fun xs => ∀ s ∈ xs, PreparedSourceVerified entries s) _ B.slots [] out
    (by simp) ?_ h
  intro x hx acc ha step hs
  split at hs
  · rename_i hn
    cases hs
    intro s hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ha s hm
    · have he := List.mem_singleton.mp hm
      subst s
      obtain ⟨e, he, _, _, hp⟩ := hv x hx hn
      exact ⟨e, he, hp⟩
  · cases hs; exact ha

private theorem shuffle_mem {α : Type} {xs ys : List α} {seed : Bytes}
    (h : shuffleWithSeed xs seed = some ys) : ∀ a ∈ ys, a ∈ xs := by
  classical
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1 = ys := by simpa [hs] using h
    have hp := shuffle_perm hs
    intro a ha
    rw [← he] at ha
    exact hp.mem_iff.mp ha

/-- Shuffling and concatenating the actual prepared source descriptors retains proof validity. -/
theorem preparedSourceLists_verified (entries : List ProofEntry) (own : Nat) (blocks : List Blk)
    (hv : ∀ B ∈ blocks, ∀ x ∈ B.slots, SourceSlotValid entries own B x)
    {out : List SrcList} (h : preparedSourceLists blocks = .ok out) :
    ∀ s ∈ out, PreparedSourceVerified entries s := by
  apply forIn_invariant (fun xs => ∀ s ∈ xs, PreparedSourceVerified entries s) _ blocks [] out
    (by simp) ?_ h
  intro B hB acc ha step hs
  obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
  have hp := slotSources_verified entries own B (hv B hB) hsrc
  split at hs
  · rename_i shuffled hsh
    obtain ⟨_, he, hs⟩ := bind_ok hs
    cases he
    cases hs
    intro s hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ha s hm
    · exact hp s (shuffle_mem hsh s hm)
  · obtain ⟨_, he, _⟩ := bind_ok hs; cases he

theorem preparedSourceLists_roots_consistent (entries : List ProofEntry) (own : Nat) (blocks : List Blk)
    (hv : ∀ B ∈ blocks, ∀ x ∈ B.slots, SourceSlotValid entries own B x)
    {out : List SrcList} (h : preparedSourceLists blocks = .ok out) :
    sourceRootsConsistent out = true :=
  sourceRootsConsistent_of_verified out entries (preparedSourceLists_verified entries own blocks hv h)

end ZkFormal.NearV3.Rcpt.Candidates
