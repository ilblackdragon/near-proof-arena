import ZkFormal.NearV3.Rcpt.Candidates.PreparedReceipts

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

private theorem forIn_preserves {α β : Type} (Q : β → Prop)
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
      exact forIn_preserves Q f xs v out hp (fun x hx => hs x (by simp [hx])) h

private theorem shuffle_subset {α : Type} {xs ys : List α} {seed : Bytes}
    (h : shuffleWithSeed xs seed = some ys) : ∀ a ∈ ys, a ∈ xs := by
  classical
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1 = ys := by simpa [hs] using h
    intro a ha
    rw [← he] at ha
    exact (shuffle_perm hs).mem_iff.mp ha

/-- Every prepared source preserves any property of the actual source-slot descriptors. -/
theorem preparedSourceLists_property (P : SrcList → Prop) (blocks : List Blk)
    (hp : ∀ B ∈ blocks, ∀ s ∈ slotDescriptors B B.slots, P s)
    {out : List SrcList} (h : preparedSourceLists blocks = .ok out) : ∀ s ∈ out, P s := by
  apply forIn_preserves (fun xs => ∀ s ∈ xs, P s) _ blocks [] out (by simp) ?_ h
  intro B hB acc ha step hs
  obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
  rw [slotSources_eq] at hsrc
  have he := Except.ok.inj hsrc
  subst srcs
  split at hs
  · rename_i shuffled hsh
    obtain ⟨_, he, hs⟩ := bind_ok hs
    cases he
    cases hs
    intro s hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ha s hm
    · exact hp B hB s (shuffle_subset hsh s hm)
  · obtain ⟨_, he, _⟩ := bind_ok hs; cases he

/-- A2's actual used-proof routing property reaches every shuffled prepared occurrence. -/
theorem preparedSourceLists_raw_routing {k : WalkD0} {w : StateWitness}
    (hv : ∀ B ∈ k.sourceBlks, ∀ x ∈ B.slots, SourceSlotValid w.entries k.H.shardId B x)
    (hr : ∀ e ∈ usedProofs k w, ∀ r ∈ e.receipts, k.L.shardOf r.receiverId = k.H.shardId)
    {out : List SrcList} (h : preparedSourceLists k.sourceBlks = .ok out) :
    ∀ s ∈ out, ∀ r ∈ (sourceEntry w.entries s).receipts,
      k.L.shardOf r.receiverId = k.H.shardId := by
  refine preparedSourceLists_property (fun s => ∀ r ∈ (sourceEntry w.entries s).receipts,
    k.L.shardOf r.receiverId = k.H.shardId) k.sourceBlks ?_ h
  intro B hB s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  by_cases hn : x.1.heightIncluded == B.hdr.height
  · simp only [hn, ↓reduceIte, List.mem_singleton] at hs
    subst s
    obtain ⟨e, he, _, _, _⟩ := hv B hB x hx hn
    have hu : e ∈ usedProofs k w := by
      apply List.mem_flatMap.mpr
      refine ⟨B, hB, List.mem_filterMap.mpr ⟨x, hx, ?_⟩⟩
      simpa only [hn, ↓reduceIte] using he
    intro r hrec
    apply hr e hu r
    simpa only [sourceEntry, he, Option.getD_some] using hrec
  · simp [hn] at hs

end ZkFormal.NearV3.Rcpt.Candidates
