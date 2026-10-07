import ZkFormal.NearV3.Rcpt.Candidates.PreparedReceipts
import ZkFormal.NearV3.Rcpt.Link.SourceNonempty
import ZkFormal.NearV3.Assembly.PreparedSources

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

private theorem new_slot_exists (B : Blk) (idx : Nat)
    (h : (match B.slots[idx]? with
      | some (s, _) => s.heightIncluded == B.hdr.height
      | none => false) = true) :
    ∃ x ∈ B.slots, (x.1.heightIncluded == B.hdr.height) = true := by
  cases hs : B.slots[idx]? with
  | none => simp [hs] at h
  | some p => exact ⟨p, List.mem_of_getElem? hs, by simpa [hs] using h⟩

private theorem source_slice_new {blks : List Blk} {b2i idx : Nat}
    (h : blks.findIdx? (fun B => match B.slots[idx]? with
      | some (s, _) => s.heightIncluded == B.hdr.height
      | none => false) = some b2i) (j : Nat) :
    ∃ B ∈ (blks.drop b2i).take ((b2i + 1 + j) - b2i),
      ∃ x ∈ B.slots, (x.1.heightIncluded == B.hdr.height) = true := by
  obtain ⟨B, hB, hn⟩ := sourceBlocks_has_new h j
  exact ⟨B, hB, new_slot_exists B idx hn⟩

private theorem source_slice_new_stop {blks : List Blk} {b2i idx j stop : Nat}
    (h : blks.findIdx? (fun B => match B.slots[idx]? with
      | some (s, _) => s.heightIncluded == B.hdr.height
      | none => false) = some b2i) (hs : b2i + 1 + j = stop) :
    ∃ B ∈ (blks.drop b2i).take (stop - b2i),
      ∃ x ∈ B.slots, (x.1.heightIncluded == B.hdr.height) = true := by
  rw [← hs]
  exact source_slice_new h j

set_option maxHeartbeats 2000000 in
/-- A successful actual native walk has a new source slot, namely B2's own slot. -/
theorem walkD0_has_source {cb : Bytes} {k : WalkD0} (h : walkD0 cb = .ok k) :
    ∃ B ∈ k.sourceBlks, ∃ x ∈ B.slots, (x.1.heightIncluded == B.hdr.height) = true := by
  unfold walkD0 at h
  repeat' (first
    | (have hh := h; clear h; obtain ⟨_, _, h⟩ := bind_ok hh; clear hh)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp_all only [pure, Except.pure, Except.ok.injEq]
    apply source_slice_new_stop <;> assumption

private theorem forIn_length_add {α β : Type} (cost : α → Nat)
    (f : α → List β → Except String (ForInStep (List β))) :
    ∀ (xs : List α) (acc out : List β),
      (∀ x ∈ xs, ∀ a step, f x a = .ok step →
        ∃ next, step = .yield next ∧ next.length = a.length + cost x) →
      forIn xs acc f = .ok out → out.length = acc.length + (xs.map cost).sum
  | [], acc, out, _, h => by cases h; simp
  | x :: xs, acc, out, hs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hf, h⟩ := bind_ok h
    obtain ⟨next, rfl, he⟩ := hs x (by simp) acc step hf
    have ht := forIn_length_add cost f xs next out (fun y hy => hs y (by simp [hy])) h
    rw [ht, he]
    simp [Nat.add_assoc]

/-- Preparation retains exactly the number of new source slots despite shuffling. -/
theorem preparedSourceLists_length (blocks : List Blk) {out : List SrcList}
    (h : preparedSourceLists blocks = .ok out) :
    out.length = (blocks.map fun B => (slotDescriptors B B.slots).length).sum := by
  have hh := forIn_length_add (fun B => (slotDescriptors B B.slots).length)
    _ blocks [] out (by
      intro B hB acc step hs
      obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
      rw [slotSources_eq] at hsrc
      cases hsrc
      split at hs
      · rename_i shuffled hsh
        obtain ⟨_, he, hs⟩ := bind_ok hs
        cases he
        cases hs
        refine ⟨_, rfl, ?_⟩
        have hlen : shuffled.length = (slotDescriptors B B.slots).length := by
          unfold shuffleWithSeed at hsh
          cases he : shuffle (slotDescriptors B B.slots) (Rng.ofSeed B.hdr.prevHash) with
          | none => simp [he] at hsh
          | some p =>
            have hp : p.1 = shuffled := by simpa [he] using hsh
            rw [← hp]
            exact length_shuffle he
        simp [hlen]
      · obtain ⟨_, he, _⟩ := bind_ok hs; cases he) h
  simpa only [List.length_nil, Nat.zero_add] using hh

private theorem one_le_sum {α : Type} (cost : α → Nat) (xs : List α) (a : α)
    (ha : a ∈ xs) : cost a ≤ (xs.map cost).sum := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha; omega

/-- Actual successful preparation cannot produce an empty source list. -/
theorem prepD0_sources_nonempty {cb : Bytes} {hint : Hint} {p : Prep} {k : WalkD0}
    (hp : prepD0 cb hint = .ok p) (hk : walkD0 cb = .ok k) : p.lists ≠ [] := by
  obtain ⟨B, hB, x, hx, hn⟩ := walkD0_has_source hk
  have hm : (⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
      x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩ : SrcList) ∈ slotDescriptors B B.slots := by
    apply List.mem_flatMap.mpr
    exact ⟨x, hx, by simp [hn]⟩
  have hc : 0 < (slotDescriptors B B.slots).length := by
    cases he : slotDescriptors B B.slots with
    | nil => simp [he] at hm
    | cons a rest => simp
  have hle := one_le_sum (fun B => (slotDescriptors B B.slots).length) k.sourceBlks B hB
  have he := preparedSourceLists_length k.sourceBlks (Assembly.prepD0_source_lists hp hk)
  intro hz
  rw [hz] at he
  simp only [List.length_nil] at he
  omega

end ZkFormal.NearV3.Rcpt.Candidates
