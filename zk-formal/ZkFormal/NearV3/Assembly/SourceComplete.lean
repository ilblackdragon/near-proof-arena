import ZkFormal.NearV3.Rcpt.Link.SourceLoop
import ZkFormal.NearV3.Assembly.Good

/-! Reconstruct successful native source-loop execution from ordinary proof
selection, Merkle verification and shuffle semantics. No checker-success premise.+-/
namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

def selectedEntries (entries : List ProofEntry) (b : Blk)
    (slots : List (ChunkSlot × ChunkInner)) : List ProofEntry :=
  slots.filterMap fun (s, ci) =>
    if s.heightIncluded == b.hdr.height then
      lookupLast (chunkHash s.inner ci.encodedMerkleRoot) entries else none

theorem checkedSourceSlots_complete (entries : List ProofEntry) (own : Nat) (b : Blk)
    (slots : List (ChunkSlot × ChunkInner))
    (hv : ∀ x ∈ slots, SourceSlotValid entries own b x) (n : Nat) (acc : List ProofEntry) :
    forIn slots (n, acc) (checkedSourceSlot entries own b) =
      .ok (n + (selectedEntries entries b slots).length, acc ++ selectedEntries entries b slots) := by
  induction slots generalizing n acc with
  | nil => simp [selectedEntries, pure, Except.pure]
  | cons x xs ih =>
    have ht : ∀ y ∈ xs, SourceSlotValid entries own b y :=
      fun y hy => hv y (List.mem_cons_of_mem _ hy)
    by_cases hn : x.1.heightIncluded == b.hdr.height
    · obtain ⟨e, he, hf, ho, hp⟩ := hv x (by simp) hn
      have hs : checkedSourceSlot entries own b x (n, acc) = .ok (.yield (n + 1, acc ++ [e])) := by
        simp [checkedSourceSlot, hn, he, hf, ho, hp, check, pure, Except.pure, bind, Except.bind, Functor.map, Except.map]
      rw [List.forIn_cons, hs]
      simp only [bind, Except.bind]
      rw [ih ht]
      have hn' := hn
      simp only [beq_iff_eq] at hn'
      simp [selectedEntries, List.filterMap_cons, hn', he, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · have hs : checkedSourceSlot entries own b x (n, acc) = .ok (.yield (n, acc)) := by
        simp [checkedSourceSlot, hn, pure, Except.pure]
      rw [List.forIn_cons, hs]
      simp only [bind, Except.bind]
      rw [ih ht]
      have hn' := hn
      simp only [beq_iff_eq] at hn'
      simp [selectedEntries, List.filterMap_cons, hn']

def blockApplied (entries : List ProofEntry) (own : Nat) (L : Layout) (b : Blk) : List Receipt :=
  let es := selectedEntries entries b b.slots
  let shuffled := (shuffleWithSeed es b.hdr.prevHash).getD es
  (shuffled.map fun e => e.receipts.filter fun r => L.shardOf r.receiverId == own).flatten

theorem checkedSourceBlock_complete (entries : List ProofEntry) (own : Nat) (L : Layout) (b : Blk)
    (hv : ∀ x ∈ b.slots, SourceSlotValid entries own b x)
    (hs : ∃ shuffled, shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled)
    (acc : List Receipt × Nat) :
    checkedSourceBlock entries own L b acc = .ok (.yield
      (acc.1 ++ blockApplied entries own L b, acc.2 + (selectedEntries entries b b.slots).length)) := by
  unfold checkedSourceBlock
  rw [checkedSourceSlots_complete entries own b b.slots hv acc.2 []]
  obtain ⟨shuffled, hs⟩ := hs
  simp [blockApplied, hs, pure, Except.pure, bind, Except.bind]

theorem checkedSourceLoop_complete (entries : List ProofEntry) (own : Nat) (L : Layout)
    (blocks : List Blk)
    (hv : ∀ b ∈ blocks, ∀ x ∈ b.slots, SourceSlotValid entries own b x)
    (hs : ∀ b ∈ blocks, ∃ shuffled,
      shuffleWithSeed (selectedEntries entries b b.slots) b.hdr.prevHash = some shuffled)
    (acc : List Receipt × Nat) :
    forIn blocks acc (checkedSourceBlock entries own L) = .ok
      (acc.1 ++ blocks.flatMap (blockApplied entries own L),
       acc.2 + (blocks.map fun b => (selectedEntries entries b b.slots).length).sum) := by
  induction blocks generalizing acc with
  | nil => simp [pure, Except.pure]
  | cons b bs ih =>
    rw [List.forIn_cons, checkedSourceBlock_complete entries own L b (hv b (by simp)) (hs b (by simp))]
    simp only [bind, Except.bind]
    rw [ih (fun b hb => hv b (List.mem_cons_of_mem _ hb)) (fun b hb => hs b (List.mem_cons_of_mem _ hb))]
    simp [List.append_assoc, Nat.add_assoc]

private theorem forInId_append {α β : Type} (f : α → List β) (xs : List α) (acc : List β) :
    (forIn xs acc (fun x a => pure (.yield (a ++ f x))) : Id (List β)) = acc ++ xs.flatMap f := by
  induction xs generalizing acc with
  | nil => simp [pure]
  | cons x xs ih =>
    rw [List.forIn_cons]
    change (forIn xs (acc ++ f x) (fun x a => pure (.yield (a ++ f x))) : Id (List β)) = _
    rw [ih]
    simp [List.append_assoc]

theorem appliedReceipts_eq_flatMap (k : WalkD0) (w : StateWitness) :
    appliedReceipts k w = k.sourceBlks.flatMap (blockApplied w.entries k.H.shardId k.L) := by
  change (forIn k.sourceBlks [] (fun b acc =>
    pure (.yield (acc ++ blockApplied w.entries k.H.shardId k.L b))) : Id (List Receipt)) = _
  simpa using forInId_append (blockApplied w.entries k.H.shardId k.L) k.sourceBlks []

def eligibleKeys (b : Blk) (slots : List (ChunkSlot × ChunkInner)) : List Bytes :=
  slots.filterMap fun (s, ci) =>
    if s.heightIncluded == b.hdr.height then some (chunkHash s.inner ci.encodedMerkleRoot) else none

theorem selectedEntries_length (entries : List ProofEntry) (own : Nat) (b : Blk)
    (slots : List (ChunkSlot × ChunkInner))
    (hv : ∀ x ∈ slots, SourceSlotValid entries own b x) :
    (selectedEntries entries b slots).length = (eligibleKeys b slots).length := by
  induction slots with
  | nil => rfl
  | cons x xs ih =>
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
    by_cases hn : x.1.heightIncluded == b.hdr.height
    · obtain ⟨e, he, _, _, _⟩ := hv x (by simp) hn
      have hn' := hn
      simp only [beq_iff_eq] at hn'
      simpa [selectedEntries, eligibleKeys, List.filterMap_cons, hn', he] using ht
    · have hn' := hn
      simp only [beq_iff_eq] at hn'
      simpa [selectedEntries, eligibleKeys, List.filterMap_cons, hn'] using ht

theorem SourceSemanticsV3.slots {k : WalkD0} {x : ExtV3} (h : SourceSemanticsV3 k x) :
    ∀ b ∈ k.sourceBlks, ∀ s ∈ b.slots,
      SourceSlotValid (x.dictionary.map DictionaryEntryV3.entry) k.H.shardId b s := by
  intro b hb s hs hn
  obtain ⟨e, _, he, hf, ht, hv⟩ := h.selected b hb s.1 s.2 hs hn
  exact ⟨e.entry, he, hf, ht, hv⟩

theorem SourceSemanticsV3.loop {k : WalkD0} {x : ExtV3} (h : SourceSemanticsV3 k x) :
    forIn k.sourceBlks ([], 0)
      (checkedSourceBlock (x.dictionary.map DictionaryEntryV3.entry) k.H.shardId k.L) =
      .ok (x.applied, (sourceKeysV3 k).length) := by
  have hl := checkedSourceLoop_complete (x.dictionary.map DictionaryEntryV3.entry) k.H.shardId
    k.L k.sourceBlks h.slots h.shuffle ([], 0)
  have ha : k.sourceBlks.flatMap
      (blockApplied (x.dictionary.map DictionaryEntryV3.entry) k.H.shardId k.L) = x.applied :=
    (appliedReceipts_eq_flatMap k (stateWitnessOfV3 k x)).symm.trans h.applied
  have hc : (k.sourceBlks.map fun b =>
      (selectedEntries (x.dictionary.map DictionaryEntryV3.entry) b b.slots).length).sum =
      (sourceKeysV3 k).length := by
    unfold sourceKeysV3
    rw [List.length_flatMap]
    congr 1
    apply List.map_congr_left
    intro b hb
    exact selectedEntries_length _ k.H.shardId b b.slots (h.slots b hb)
  simpa only [List.nil_append, Nat.zero_add, ha, hc] using hl

end ZkFormal.NearV3.Assembly
