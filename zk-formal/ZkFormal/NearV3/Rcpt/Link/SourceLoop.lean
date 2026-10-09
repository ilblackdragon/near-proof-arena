import ZkFormal.NearV3.Rcpt.Link.CheckSources

namespace ZkFormal.NearV3
open NearSpec NearSpecV3 Sched

/-- The validator's actual per-slot computation, with its original accumulator. -/
def checkedSourceSlot (entries : List ProofEntry) (own : Nat) (B : Blk)
    (x : ChunkSlot × ChunkInner) (acc : Nat × List ProofEntry) :
    Except String (ForInStep (Nat × List ProofEntry)) := do
  if x.1.heightIncluded == B.hdr.height then
    let e ← match lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot) entries with
      | some e => pure e
      | none => throw "invalid: missing source receipt proof"
    check (e.proof.fromShard == x.2.shardId) "invalid: receipt proof from_shard_id"
    check (e.proof.toShard == own) "invalid: receipt proof to_shard_id"
    check (verifyReceiptProof x.2.prevOutgoingReceiptsRoot e) "invalid: receipt proof merkle path"
    pure (.yield (acc.1 + 1, acc.2 ++ [e]))
  else pure (.yield acc)

def SourceSlotValid (entries : List ProofEntry) (own : Nat) (B : Blk)
    (x : ChunkSlot × ChunkInner) : Prop :=
  x.1.heightIncluded == B.hdr.height →
    ∃ e, lookupLast (chunkHash x.1.inner x.2.encodedMerkleRoot) entries = some e ∧
      e.proof.fromShard = x.2.shardId ∧ e.proof.toShard = own ∧
      verifyReceiptProof x.2.prevOutgoingReceiptsRoot e = true

private theorem sourceSlot_step (entries : List ProofEntry) (own : Nat) (B : Blk)
    (x : ChunkSlot × ChunkInner) (acc : Nat × List ProofEntry)
    {step : ForInStep (Nat × List ProofEntry)}
    (h : checkedSourceSlot entries own B x acc = .ok step) :
    (∃ next, step = .yield next) ∧ SourceSlotValid entries own B x := by
  unfold checkedSourceSlot at h
  split at h
  · rename_i hn
    split at h
    · rename_i e he
      obtain ⟨_, hp, h⟩ := bind_ok h
      cases hp
      obtain ⟨_, hf, h⟩ := bind_ok h
      obtain ⟨_, ht, h⟩ := bind_ok h
      obtain ⟨_, hv, h⟩ := bind_ok h
      cases h
      exact ⟨⟨_, rfl⟩, fun _ => ⟨e, he, by simpa using check_ok hf,
        by simpa using check_ok ht, check_ok hv⟩⟩
    · obtain ⟨_, he, _⟩ := bind_ok h; cases he
  · rename_i hn
    cases h
    exact ⟨⟨_, rfl⟩, fun hh => False.elim (hn hh)⟩

/-- A successful loop whose steps always yield has checked every input, not merely a prefix. -/
theorem forIn_all_yield {α β : Type} (P : α → Prop)
    (f : α → β → Except String (ForInStep β))
    (hs : ∀ a b step, f a b = .ok step → (∃ next, step = .yield next) ∧ P a) :
    ∀ (xs : List α) (start out : β), forIn xs start f = .ok out → ∀ a ∈ xs, P a
  | [], _, _, _, _, ha => by simp at ha
  | x :: xs, start, out, h, a, ha => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hf, h⟩ := bind_ok h
    obtain ⟨⟨next, rfl⟩, hp⟩ := hs x start step hf
    rcases List.mem_cons.mp ha with he | hm
    · simpa only [he] using hp
    · exact forIn_all_yield P f hs xs next out h a hm

def checkedSourceBlock (entries : List ProofEntry) (own : Nat) (L : Layout)
    (B : Blk) (acc : List Receipt × Nat) : Except String (ForInStep (List Receipt × Nat)) := do
  let out ← forIn B.slots (acc.2, []) (checkedSourceSlot entries own B)
  let shuffled ← match shuffleWithSeed out.2 B.hdr.prevHash with
    | some p => pure p
    | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
  pure (.yield (acc.1 ++ (shuffled.map fun e => e.receipts.filter
    fun r => L.shardOf r.receiverId == own).flatten, out.1))

private theorem sourceBlock_step (entries : List ProofEntry) (own : Nat) (L : Layout)
    (B : Blk) (acc : List Receipt × Nat) {step : ForInStep (List Receipt × Nat)}
    (h : checkedSourceBlock entries own L B acc = .ok step) :
    (∃ next, step = .yield next) ∧ ∀ x ∈ B.slots, SourceSlotValid entries own B x := by
  unfold checkedSourceBlock at h
  obtain ⟨out, ho, h⟩ := bind_ok h
  have hv := forIn_all_yield (SourceSlotValid entries own B) _
    (sourceSlot_step entries own B) B.slots (acc.2, []) out ho
  split at h
  · obtain ⟨_, hp, h⟩ := bind_ok h
    cases hp
    cases h
    exact ⟨⟨_, rfl⟩, hv⟩
  · obtain ⟨_, he, _⟩ := bind_ok h; cases he

/-- Successful original nested source-loop computation verifies every selected proof. -/
theorem checkedSourceLoop_valid (entries : List ProofEntry) (own : Nat) (L : Layout)
    (blocks : List Blk) {out : List Receipt × Nat}
    (h : forIn blocks ([], 0) (checkedSourceBlock entries own L) = .ok out) :
    ∀ B ∈ blocks, ∀ x ∈ B.slots, SourceSlotValid entries own B x :=
  forIn_all_yield _ _ (sourceBlock_step entries own L) blocks ([], 0) out h

end ZkFormal.NearV3
