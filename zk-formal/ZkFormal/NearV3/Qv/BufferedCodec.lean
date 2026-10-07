import ZkFormal.NearV3.Qv.Queue
import NearSpecV3.ClaimV3Props
import ReexecV3D0.NormBytes

/-! Exact codec of BufferedReceiptIndices. No sorting or uniqueness condition
is added: the reference parser accepts its vector in serialized order. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3 ReexecV3D0

abbrev BufferEntry := Nat × Nat × Nat

def bufferEntryParser : P BufferEntry := fun bs => do
  let (s,bs) ← pU64 "shard" bs
  let (f,bs) ← pU64 "first" bs
  let (n,bs) ← pU64 "next" bs
  pure ((s,f,n),bs)

def bufferEntryBytes (e : BufferEntry) : Bytes := u64 e.1 ++ u64 e.2.1 ++ u64 e.2.2

def BufferEntrySized (e : BufferEntry) : Prop :=
  e.1 < 256^8 ∧ e.2.1 < 256^8 ∧ e.2.2 < 256^8

def bufferedBytes (es : List BufferEntry) : Bytes := encList bufferEntryBytes es

theorem bufferEntryParser_encode (e : BufferEntry) (he : BufferEntrySized e) (rest : Bytes) :
    bufferEntryParser (bufferEntryBytes e ++ rest) = .ok (e,rest) := by
  rcases e with ⟨s,f,n⟩
  obtain ⟨hs,hf,hn⟩ := he
  simp only [bufferEntryParser,bufferEntryBytes,List.append_assoc,pU64_ok _ _ _ hs,
    bind,Except.bind,pU64_ok _ _ _ hf,pU64_ok _ _ _ hn,pure,Except.pure]

theorem bufferEntryParser_inv {bs rest : Bytes} {e : BufferEntry}
    (h : bufferEntryParser bs = .ok (e,rest)) :
    bs = bufferEntryBytes e ++ rest ∧ BufferEntrySized e := by
  unfold bufferEntryParser at h
  obtain ⟨⟨s,b1⟩,h1,h⟩ := bind_ok' h
  obtain ⟨⟨f,b2⟩,h2,h⟩ := bind_ok' h
  obtain ⟨⟨n,b3⟩,h3,h⟩ := bind_ok' h
  simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
  obtain ⟨rfl,rfl⟩ := h
  obtain ⟨e1,hs⟩ := lift_readLE_inv h1
  obtain ⟨e2,hf⟩ := lift_readLE_inv h2
  obtain ⟨e3,hn⟩ := lift_readLE_inv h3
  refine ⟨?_,hs,hf,hn⟩
  rw [e1,e2,e3]
  simp only [bufferEntryBytes,u64,List.append_assoc]

theorem bufferMany_inv : ∀ (n : Nat) {bs rest : Bytes} {es : List BufferEntry},
    pMany bufferEntryParser n bs = .ok (es,rest) →
      bs = (es.flatMap bufferEntryBytes) ++ rest ∧ es.length=n ∧ ∀ e ∈ es, BufferEntrySized e
  | 0, bs, rest, es, h => by
    simp only [pMany,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    simp
  | n+1, bs, rest, es, h => by
    simp only [pMany] at h
    obtain ⟨⟨e,b1⟩,h1,h⟩ := bind_ok' h
    obtain ⟨⟨tail,b2⟩,h2,h⟩ := bind_ok' h
    simp only [pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl⟩ := h
    dsimp only at h2
    obtain ⟨e1,he⟩ := bufferEntryParser_inv h1
    obtain ⟨e2,hn,ht⟩ := bufferMany_inv n h2
    refine ⟨?_,by simp [hn],?_⟩
    · rw [e1,e2,List.flatMap_cons,List.append_assoc]
    · intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact ht e' he'

private theorem bufferConcat (es : List BufferEntry) :
    concatAll (es.map bufferEntryBytes) = es.flatMap bufferEntryBytes := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [concatAll,ih]

theorem bufferVec_inv {bs rest : Bytes} {es : List BufferEntry}
    (h : pVec "shard_buffers" bufferEntryParser bs = .ok (es,rest)) :
    bs = bufferedBytes es ++ rest ∧ es.length < 256^4 ∧ ∀ e ∈ es, BufferEntrySized e := by
  unfold pVec at h
  obtain ⟨⟨n,b1⟩,h1,h⟩ := bind_ok' h
  obtain ⟨e1,hn⟩ := lift_readLE_inv h1
  obtain ⟨e2,hlen,hs⟩ := bufferMany_inv n h
  refine ⟨?_,by omega,hs⟩
  rw [e1,e2,← hlen]
  simp only [bufferedBytes,encList,u32,bufferConcat,List.append_assoc]

end ZkFormal.NearV3.Qv
