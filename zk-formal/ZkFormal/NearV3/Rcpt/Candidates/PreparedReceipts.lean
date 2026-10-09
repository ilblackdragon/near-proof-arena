import ZkFormal.NearV3.Rcpt.Candidates.PreparedVerified
import ZkFormal.NearV3.Sched.Spec.Rounds

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

/-- Read the selected dictionary entry of a prepared source. Validated source selection
proves the fallback is never used. -/
def sourceEntry (entries : List ProofEntry) (s : SrcList) : ProofEntry :=
  (lookupLast s.key entries).getD ⟨[],[],⟨0,0,[]⟩⟩

def slotDescriptors (B : Blk) (slots : List (ChunkSlot × ChunkInner)) : List SrcList :=
  slots.flatMap fun x => if x.1.heightIncluded == B.hdr.height then
    [⟨chunkHash x.1.inner x.2.encodedMerkleRoot, x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩] else []

private theorem forIn_append {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (acc : List β),
      (forIn xs acc (fun x a => pure (.yield (a ++ f x))) : Except String (List β)) =
        .ok (acc ++ xs.flatMap f)
  | [], acc => by simp [pure, Except.pure]
  | x :: xs, acc => by
    rw [List.forIn_cons]
    change (forIn xs (acc ++ f x) (fun x a => pure (.yield (a ++ f x))) : Except String (List β)) = _
    rw [forIn_append]
    simp [List.append_assoc]

/-- Exact output of the real prepared per-block slot loop. -/
theorem slotSources_eq (B : Blk) : slotSources B = .ok (slotDescriptors B B.slots) := by
  have he : (fun (x : ChunkSlot × ChunkInner) (acc : List SrcList) =>
      if x.1.heightIncluded == B.hdr.height then
        (pure (.yield (acc ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
          x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩])) : Except String (ForInStep (List SrcList)))
      else pure (.yield acc)) =
      (fun x acc => pure (.yield (acc ++ if x.1.heightIncluded == B.hdr.height then
        [⟨chunkHash x.1.inner x.2.encodedMerkleRoot, x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩] else []))) := by
    funext x acc
    split <;> simp_all
  unfold slotSources
  rw [he, forIn_append]
  rfl

def selectedProofs (entries : List ProofEntry) (B : Blk)
    (slots : List (ChunkSlot × ChunkInner)) : List ProofEntry :=
  slots.filterMap fun x => if x.1.heightIncluded == B.hdr.height then
    lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot) entries else none

/-- Mapping prepared source keys through the same dictionary gives exactly the
validator's selected proof sequence before shuffling. -/
theorem slotDescriptors_selected (entries : List ProofEntry) (own : Nat) (B : Blk)
    (slots : List (ChunkSlot × ChunkInner))
    (hv : ∀ x ∈ slots, SourceSlotValid entries own B x) :
    (slotDescriptors B slots).map (sourceEntry entries) = selectedProofs entries B slots := by
  induction slots with
  | nil => rfl
  | cons x rest ih =>
    have ht := ih (fun y hy => hv y (by simp [hy]))
    by_cases hn : x.1.heightIncluded == B.hdr.height
    · obtain ⟨e, he, _, _, _⟩ := hv x (by simp) hn
      simp only [slotDescriptors, List.flatMap_cons, hn, ↓reduceIte, List.singleton_append,
        List.map_cons, sourceEntry, he, Option.getD_some, selectedProofs, List.filterMap_cons]
      exact congrArg (List.cons e) ht
    · simp only [slotDescriptors, List.flatMap_cons, hn, ↓reduceIte, List.nil_append,
        selectedProofs, List.filterMap_cons]
      exact ht

theorem shuffleWithSeed_map {α β : Type} (f : α → β) (xs : List α) (seed : Bytes) :
    shuffleWithSeed (xs.map f) seed = (shuffleWithSeed xs seed).map (List.map f) := by
  unfold shuffleWithSeed
  rw [shuffle_map]
  simp only [Option.map_map, Function.comp_def]

def sourceReceipts (entries : List ProofEntry) (own : Nat) (L : Layout) (s : SrcList) : List Receipt :=
  (sourceEntry entries s).receipts.filter fun r => L.shardOf r.receiverId == own

def sourceBlockReceipts (entries : List ProofEntry) (own : Nat) (L : Layout) (B : Blk) : List Receipt :=
  let proofs := selectedProofs entries B B.slots
  ((shuffleWithSeed proofs B.hdr.prevHash).getD proofs).flatMap fun e =>
    e.receipts.filter fun r => L.shardOf r.receiverId == own

/-- The actual prepared shuffle commutes with dictionary lookup, including repeated keys. -/
theorem shuffled_source_receipts (entries : List ProofEntry) (own : Nat) (L : Layout) (B : Blk)
    (hv : ∀ x ∈ B.slots, SourceSlotValid entries own B x)
    {srcs shuffled : List SrcList} (hs : slotSources B = .ok srcs)
    (hsh : shuffleWithSeed srcs B.hdr.prevHash = some shuffled) :
    shuffled.flatMap (sourceReceipts entries own L) = sourceBlockReceipts entries own L B := by
  rw [slotSources_eq] at hs
  have hsrc := Except.ok.inj hs
  have hm := slotDescriptors_selected entries own B B.slots hv
  rw [hsrc] at hm
  have hproof : shuffleWithSeed (selectedProofs entries B B.slots) B.hdr.prevHash =
      some (shuffled.map (sourceEntry entries)) := by
    rw [← hm, shuffleWithSeed_map, hsh]
    rfl
  simp only [sourceBlockReceipts, hproof, Option.getD_some, List.flatMap_map, Function.comp_def,
    sourceReceipts]
  rfl

private theorem forIn_mapped_append {α β γ : Type} (g : β → List γ) (piece : α → List γ)
    (f : α → List β → Except String (ForInStep (List β))) :
    ∀ (xs : List α) (acc out : List β),
      (∀ x ∈ xs, ∀ a step, f x a = .ok step →
        ∃ next, step = .yield next ∧ next.flatMap g = a.flatMap g ++ piece x) →
      forIn xs acc f = .ok out → out.flatMap g = acc.flatMap g ++ xs.flatMap piece
  | [], acc, out, _, h => by cases h; simp
  | x :: xs, acc, out, hs, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hf, h⟩ := bind_ok h
    obtain ⟨next, rfl, he⟩ := hs x (by simp) acc step hf
    have ht := forIn_mapped_append g piece f xs next out
      (fun y hy => hs y (by simp [hy])) h
    rw [ht, he]
    simp [List.append_assoc]

/-- The complete prepared-source loop preserves exact shuffled receipt application. -/
theorem preparedSourceLists_receipts (entries : List ProofEntry) (own : Nat) (L : Layout)
    (blocks : List Blk) (hv : ∀ B ∈ blocks, ∀ x ∈ B.slots, SourceSlotValid entries own B x)
    {out : List SrcList} (h : preparedSourceLists blocks = .ok out) :
    out.flatMap (sourceReceipts entries own L) = blocks.flatMap (sourceBlockReceipts entries own L) := by
  have hh := forIn_mapped_append (sourceReceipts entries own L) (sourceBlockReceipts entries own L)
    _ blocks [] out (by
      intro B hB acc step hs
      obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
      split at hs
      · rename_i shuffled hsh
        obtain ⟨_, he, hs⟩ := bind_ok hs
        cases he
        cases hs
        refine ⟨_, rfl, ?_⟩
        rw [List.flatMap_append, shuffled_source_receipts entries own L B (hv B hB) hsrc hsh]
      · obtain ⟨_, he, _⟩ := bind_ok hs; cases he) h
  simpa only [List.flatMap_nil, List.nil_append] using hh

private theorem forInId_append {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (acc : List β),
      (forIn xs acc (fun x a => pure (.yield (a ++ f x))) : Id (List β)) =
        acc ++ xs.flatMap f
  | [], acc => by simp [pure, Except.pure]
  | x :: xs, acc => by
    rw [List.forIn_cons]
    change (forIn xs (acc ++ f x) (fun x a => pure (.yield (a ++ f x))) : Id (List β)) = _
    rw [forInId_append]
    simp [List.append_assoc]

theorem appliedReceipts_sourceBlocks (k : WalkD0) (w : StateWitness) :
    appliedReceipts k w = k.sourceBlks.flatMap (sourceBlockReceipts w.entries k.H.shardId k.L) := by
  change (forIn k.sourceBlks [] (fun B acc =>
    pure (.yield (acc ++ sourceBlockReceipts w.entries k.H.shardId k.L B))) : Id (List Receipt)) = _
  simpa using forInId_append (sourceBlockReceipts w.entries k.H.shardId k.L) k.sourceBlks []

/-- Exact prepared-to-native receipt-list binding, including the actual shuffle seed. -/
theorem preparedSourceLists_applied {k : WalkD0} {w : StateWitness}
    (hv : ∀ B ∈ k.sourceBlks, ∀ x ∈ B.slots, SourceSlotValid w.entries k.H.shardId B x)
    {out : List SrcList} (h : preparedSourceLists k.sourceBlks = .ok out) :
    out.flatMap (sourceReceipts w.entries k.H.shardId k.L) = appliedReceipts k w := by
  rw [appliedReceipts_sourceBlocks]
  exact preparedSourceLists_receipts w.entries k.H.shardId k.L k.sourceBlks hv h

end ZkFormal.NearV3.Rcpt.Candidates
