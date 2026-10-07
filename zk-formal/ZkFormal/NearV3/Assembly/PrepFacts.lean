import ZkFormal.NearV3.Sched.Pub.Prep
import ZkFormal.NearV3.Public.Header
import ZkFormal.V3.RefundCodec

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

end ZkFormal.NearV3.Assembly
