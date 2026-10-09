import ZkFormal.NearV3.Sched.Spec.Rounds

/-!
# Why source-proof blocks are nonempty

`prepClaim` finds B2 at `b2i` and sets `stop = b2i + 1 + j` for the
last-but-one new chunk. Therefore its exact source-block slice includes B2.
B2's own slot contributes a source proof, even when that proof has no receipts;
shuffling cannot erase it. These are structural lemmas for the eventual
`prepClaim` success decomposition, not yet that end-to-end theorem.
-/

namespace ZkFormal.NearV3

open NearSpecV3

/-- The exact source-block slice used by `prepClaim` contains B2. -/
theorem sourceBlocks_b2_mem {α : Type} {bs : List α} {b2i : Nat}
    (hi : b2i < bs.length) (j : Nat) :
    bs[b2i] ∈ (bs.drop b2i).take ((b2i + 1 + j) - b2i) := by
  apply List.mem_take_iff_getElem.mpr
  refine ⟨0, by simp only [List.length_drop]; omega, ?_⟩
  simp

/-- Finding B2 supplies a new source block in the slice, independently of receipts. -/
theorem sourceBlocks_has_new {α : Type} {bs : List α} {isNew : α → Bool}
    {b2i : Nat} (h : bs.findIdx? isNew = some b2i) (j : Nat) :
    ∃ B ∈ (bs.drop b2i).take ((b2i + 1 + j) - b2i), isNew B = true := by
  obtain ⟨hi, hnew, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨bs[b2i], sourceBlocks_b2_mem hi j, hnew⟩

/-- B2's own new slot appears in the source-slot filter used by preparation. -/
theorem new_slot_filter_nonempty (B : Blk) (idx : Nat)
    (hnew : (match B.slots[idx]? with
      | some (s, _) => s.heightIncluded == B.hdr.height
      | none => false) = true) :
    B.slots.filter (fun p => p.1.heightIncluded == B.hdr.height) ≠ [] := by
  cases hs : B.slots[idx]? with
  | none => simp [hs] at hnew
  | some p =>
    have hp : p ∈ B.slots := List.mem_of_getElem? hs
    have hf : p ∈ B.slots.filter (fun p => p.1.heightIncluded == B.hdr.height) := by
      apply List.mem_filter.mpr
      exact ⟨hp, by simpa [hs] using hnew⟩
    intro he
    rw [he] at hf
    simp at hf

/-- The actual seeded shuffle retains a nonempty source list. -/
theorem source_shuffle_nonempty {α : Type} {srcs shuffled : List α} {seed : List UInt8}
    (hne : srcs ≠ []) (hsh : shuffleWithSeed srcs seed = some shuffled) :
    shuffled ≠ [] := by
  unfold shuffleWithSeed at hsh
  cases h : shuffle srcs (Rng.ofSeed seed) with
  | none => simp [h] at hsh
  | some p =>
    have he : p.1 = shuffled := by simpa [h] using hsh
    have hl := Sched.length_shuffle h
    intro hz
    rw [he, hz] at hl
    exact hne (by simpa using hl.symm)

end ZkFormal.NearV3
