import ZkFormal.NearV3.Candidates.ProcPrepBudget
import ZkFormal.NearV3.Assembly.HeaderWireShape
namespace ZkFormal.NearV3.Candidates.ProcBitmapShape
open NearSpec NearSpecV3 ZkFormal.NearV3.Sched ZkFormal.NearV3.Assembly

def ChunkBits (ci : ChunkInner) : Prop := ∀q∈ci.bwRequests,q.bitmap.length=5

theorem chunk_parser {bs rest : Bytes} {ci : ChunkInner}
    (h : pChunkInner bs=.ok (ci,rest)) : ChunkBits ci := by
  unfold pChunkInner at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    intro q hq
    have hb := (pBwRequests_shape (by assumption)).2
    have hh := List.all_eq_true.mp hb q hq
    simp only [ZkFormal.V3.bwRequestWf,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hh
    exact hh.2

theorem chunk_decode {bs : Bytes} {ci : ChunkInner}
    (h : decodeChunkInner bs=.ok ci) : ChunkBits ci := by
  unfold decodeChunkInner at h
  obtain ⟨⟨v,rest⟩,hp,h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  · cases h
    exact chunk_parser hp

def BlockBits (b : Blk) : Prop := ∀p∈b.slots,ChunkBits p.2

theorem block_decode {r : BlockRec} {b : Blk} (h : decodeBlk r=.ok b) : BlockBits b := by
  unfold decodeBlk at h
  obtain ⟨hdr,hh,h⟩ := bind_ok h
  obtain ⟨slots,hs,h⟩ := bind_ok h
  obtain ⟨u,hu,h⟩ := bind_ok h
  cases h
  intro p hp
  obtain ⟨s,hm,he⟩ := mapM_ok _ _ _ hs p hp
  obtain ⟨ci,hci,he⟩ := bind_ok he
  cases he
  exact chunk_decode hci
end ZkFormal.NearV3.Candidates.ProcBitmapShape
