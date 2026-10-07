import ZkFormal.NearV3.Sched.Pub.Prep
import ZkFormal.NearV3.Public.Header
import ZkFormal.V3.RefundCodec
import ZkFormal.NearV3.Sched.Spec.Loop

/-! Concrete shape facts extracted from successful native preprocessing. -/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3 Sched

theorem pChunkInner_roots {bs rest : Bytes} {ci : ChunkInner}
    (h : pChunkInner bs = .ok (ci, rest)) :
    ci.prevStateRoot.length = 32 ∧ ci.prevOutcomeRoot.length = 32 ∧
      ci.prevOutgoingReceiptsRoot.length = 32 := by
  unfold pChunkInner at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨V3.pHash_len (by assumption), V3.pHash_len (by assumption),
      V3.pHash_len (by assumption)⟩

theorem decodeChunkInner_roots {bs : Bytes} {ci : ChunkInner}
    (h : decodeChunkInner bs = .ok ci) :
    ci.prevStateRoot.length = 32 ∧ ci.prevOutcomeRoot.length = 32 ∧
      ci.prevOutgoingReceiptsRoot.length = 32 := by
  unfold decodeChunkInner at h
  obtain ⟨⟨ci', rest⟩, hc, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, he, _⟩ := bind_ok h
    cases he
  · cases h
    exact pChunkInner_roots hc

theorem prepBody_shape {pc : PrepC} {hint : Hint} {p : Prep}
    (h : prepBody pc hint = .ok p) :
    p.hdr.K = pc.hdr.K ∧ p.sched = pc.sched ∧ p.lists = pc.lists ∧
      p.hdr.prevStateRoot = pc.hdr.prevStateRoot ∧
      p.hdr.postStateRoot = pc.hdr.postStateRoot ∧ p.hdr.outcomeRoot = pc.hdr.outcomeRoot := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩)
    | (cases h)

set_option maxHeartbeats 4000000 in
theorem prepClaim_sched_count {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    pc.sched.length = pc.hdr.K + 1 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have he := mapM_length _ _ _ (by assumption)
    simpa only [List.length_cons, List.length_map, Nat.add_comm] using he

theorem prepD0_sched_count {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepD0 cb hint = .ok p) : p.sched.length = p.hdr.K + 1 := by
  unfold prepD0 at h
  obtain ⟨pc, hc, hb⟩ := bind_ok h
  obtain ⟨hK, hs, _⟩ := prepBody_shape hb
  rw [hK, hs]
  exact prepClaim_sched_count hc

theorem decodeBlk_roots {r : BlockRec} {b : Blk} (h : decodeBlk r = .ok b) :
    ∀ s ci, (s, ci) ∈ b.slots → ci.prevStateRoot.length = 32 ∧
      ci.prevOutcomeRoot.length = 32 ∧ ci.prevOutgoingReceiptsRoot.length = 32 := by
  unfold decodeBlk at h
  obtain ⟨hdr, _, h⟩ := bind_ok h
  obtain ⟨slots, hm, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  intro s ci hmem
  obtain ⟨slot, _, hc⟩ := mapM_ok _ _ _ hm (s, ci) hmem
  obtain ⟨ci', hd, hc⟩ := bind_ok hc
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hc
  rcases hc with ⟨rfl, rfl⟩
  exact decodeChunkInner_roots hd

private theorem mapError_ok {ε ε' α : Type} {x : Except ε α} {f : ε → ε'} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x <;> cases h
  rfl

private theorem roots_close {rs : List BlockRec} {blks : List Blk} {i idx : Nat}
    {b B2 : Blk} {pair : ChunkSlot × ChunkInner} {slot : ChunkInner}
    (hps : (pure pair.2 : Except String ChunkInner) = .ok slot)
    (hs : B2.slots[idx]? = some pair)
    (hpb : (pure b : Except String Blk) = .ok B2)
    (hb : blks[i]? = some b) (hm : rs.mapM decodeBlk = .ok blks) :
    slot.prevStateRoot.length = 32 := by
  cases hps
  cases hpb
  obtain ⟨r, _, hd⟩ := mapM_ok _ _ _ hm b (List.mem_of_getElem? hb)
  exact (decodeBlk_roots hd pair.1 pair.2 (List.mem_of_getElem? hs)).1

set_option maxHeartbeats 4000000 in
theorem prepClaim_roots {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    pc.hdr.prevStateRoot.length = 32 ∧ pc.hdr.postStateRoot.length = 32 ∧
      pc.hdr.outcomeRoot.length = 32 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨?_, ?_, ?_⟩
    · exact roots_close (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    · exact (decodeChunkInner_roots (mapError_ok (by assumption))).1
    · exact (decodeChunkInner_roots (mapError_ok (by assumption))).2.1

theorem prepD0_roots {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepD0 cb hint = .ok p) : Public.RootsSized p := by
  unfold prepD0 at h
  obtain ⟨pc, hc, hb⟩ := bind_ok h
  obtain ⟨_, _, _, hpre, hpost, hout⟩ := prepBody_shape hb
  unfold Public.RootsSized
  rw [hpre, hpost, hout]
  exact prepClaim_roots hc

private theorem forIn_post {α β : Type} (P : β → Prop)
    (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α) (b out : β), P b →
      (∀ a ∈ xs, ∀ b step, P b → f a b = .ok step →
        match step with | .done v => P v | .yield v => P v) →
      forIn xs b f = .ok out → P out
  | [], b, out, hb, _, h => by
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | a :: xs, b, out, hb, hf, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, h⟩ := bind_ok h
    have hp := hf a (by simp) b step hb hs
    cases step with
    | done v => cases h; exact hp
    | yield v =>
      exact forIn_post P f xs v out hp (fun a ha => hf a (by simp [ha])) h

private theorem shuffle_roots {xs ys : List SrcList} {seed : Bytes}
    (hx : ∀ s ∈ xs, s.root.length = 32) (h : shuffleWithSeed xs seed = some ys) :
    ∀ s ∈ ys, s.root.length = 32 := by
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1 = ys := by simpa [hs] using h
    have hp := shuffle_perm hs
    intro s hmem
    apply hx s
    exact hp.mem_iff.mp (he ▸ hmem)

private theorem slotSources_roots (B : Blk)
    (hb : ∀ x ∈ B.slots, x.2.prevOutgoingReceiptsRoot.length = 32)
    {out : List SrcList}
    (h : (forIn B.slots [] fun x acc =>
      if x.1.heightIncluded == B.hdr.height then
        pure (.yield (acc ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
          x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩]))
      else pure (.yield acc) : Except String (List SrcList)) = .ok out) :
    ∀ s ∈ out, s.root.length = 32 := by
  apply forIn_post (fun l => ∀ s ∈ l, s.root.length = 32) _ _ _ _ (by simp) ?_ h
  intro x hx acc step ha hs
  split at hs
  · cases hs
    intro s hmem
    rcases List.mem_append.1 hmem with hm | hm
    · exact ha s hm
    · simpa using (List.mem_singleton.1 hm ▸ hb x hx)
  · cases hs; exact ha

private theorem sourceLists_roots {blocks : List Blk}
    (hb : ∀ B ∈ blocks, ∀ x ∈ B.slots, x.2.prevOutgoingReceiptsRoot.length = 32)
    {out : List SrcList}
    (h : (forIn blocks [] fun B acc => do
      let srcs ← forIn B.slots [] fun x srcs =>
        if x.1.heightIncluded == B.hdr.height then
          pure (.yield (srcs ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
            x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩]))
        else pure (.yield srcs)
      let shuffled ← match shuffleWithSeed srcs B.hdr.prevHash with
        | some p => pure p
        | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
      pure (.yield (acc ++ shuffled)) : Except String (List SrcList)) = .ok out) :
    ∀ s ∈ out, s.root.length = 32 := by
  apply forIn_post (fun l => ∀ s ∈ l, s.root.length = 32) _ _ _ _ (by simp) ?_ h
  intro B hB acc step ha hs
  obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
  have hr := slotSources_roots B (hb B hB) hsrc
  split at hs
  · rename_i p hp
    obtain ⟨shuffled, he, hs⟩ := bind_ok hs
    cases he
    cases hs
    intro s hmem
    rcases List.mem_append.1 hmem with hm | hm
    · exact ha s hm
    · exact shuffle_roots hr hp s hm
  · obtain ⟨_, he, _⟩ := bind_ok hs
    cases he

private theorem sourceBlocks_roots {rs : List BlockRec} {blks : List Blk}
    (hm : rs.mapM decodeBlk = .ok blks) (start count : Nat) :
    ∀ B ∈ (blks.drop start).take count, ∀ x ∈ B.slots,
      x.2.prevOutgoingReceiptsRoot.length = 32 := by
  intro B hB x hx
  have hmem := List.mem_of_mem_drop (List.mem_of_mem_take hB)
  obtain ⟨r, _, hd⟩ := mapM_ok _ _ _ hm B hmem
  exact (decodeBlk_roots hd x.1 x.2 hx).2.2

set_option maxHeartbeats 4000000 in
theorem prepClaim_source_roots {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∀ s ∈ pc.lists, s.root.length = 32 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    apply sourceLists_roots ?_ (by assumption)
    exact sourceBlocks_roots (by assumption) _ _

theorem prepD0_source_roots {cb : Bytes} {hint : Hint} {p : Prep}
    (h : prepD0 cb hint = .ok p) : ∀ s ∈ p.lists, s.root.length = 32 := by
  unfold prepD0 at h
  obtain ⟨pc, hc, hb⟩ := bind_ok h
  rw [(prepBody_shape hb).2.2.1]
  exact prepClaim_source_roots hc

end ZkFormal.NearV3.Assembly
