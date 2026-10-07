import ZkFormal.NearV3.Qv.BufferedCodec

/-! The exact accepted buffered-queue value: bounded triples with equal queue
indices, preserving all shard IDs including repetitions and their order. -/
namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3 ReexecV3D0

def EmptyBuffers (es : List BufferEntry) : Prop := ∀ e ∈ es, e.2.1=e.2.2

theorem emptyBuffers_any (es : List BufferEntry) (he : EmptyBuffers es) :
    es.any (fun e => e.2.1 != e.2.2) = false := by
  apply List.any_eq_false.mpr
  intro e he'
  simp [he e he']

theorem bufferedShards_encode (es : List BufferEntry) (hn : es.length < 256^4)
    (hs : ∀ e ∈ es, BufferEntrySized e) (he : EmptyBuffers es) :
    bufferedShards (some (bufferedBytes es)) = .ok (es.map (·.1)) := by
  have hd := pVec_ok "shard_buffers" bufferEntryParser bufferEntryBytes es [] hn
    (fun e he rest => bufferEntryParser_encode e (hs e he) rest)
  simp only [List.append_nil] at hd
  change pVec "shard_buffers" _ (bufferedBytes es) = _ at hd
  have hempty := emptyBuffers_any es he
  unfold bufferedShards
  change (do
    let (rows,rest) ← pVec "shard_buffers" bufferEntryParser (bufferedBytes es)
    if !rest.isEmpty then throw "invalid: StorageInconsistentState (BufferedReceiptIndices)"
    if rows.any (fun e => e.2.1 != e.2.2) then throw "out of domain (e.queues_empty): outgoing buffer not empty"
    pure (rows.map (fun e : BufferEntry => e.1))) = .ok (es.map (·.1))
  simp only [hd,bind,Except.bind,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    hempty,pure,Except.pure]

theorem bufferedShards_inv {bs : Bytes} {shards : List Nat}
    (h : bufferedShards (some bs) = .ok shards) :
    ∃ es : List BufferEntry, bs = bufferedBytes es ∧ es.length < 256^4 ∧
      (∀ e ∈ es, BufferEntrySized e) ∧ EmptyBuffers es ∧ shards = es.map (·.1) := by
  unfold bufferedShards at h
  obtain ⟨⟨es,rest⟩,hd,h⟩ := bind_ok' h
  change pVec "shard_buffers" bufferEntryParser bs = .ok (es,rest) at hd
  dsimp only at h
  cases rest with
  | cons b rest => simp at h; cases h
  | nil =>
    simp only [List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte] at h
    cases ha : es.any (fun e => e.2.1 != e.2.2) with
    | true => simp [ha] at h; cases h
    | false =>
      simp only [ha,Bool.false_eq_true,↓reduceIte,pure,Except.pure,Except.ok.injEq] at h
      obtain ⟨hb,hn,hs⟩ := bufferVec_inv hd
      refine ⟨es,by simpa using hb,hn,hs,?_,h.symm⟩
      intro e he
      have he := List.any_eq_false.mp ha e he
      simpa using he

def BufferedValue (v : Option Bytes) (shards : List Nat) : Prop :=
  match v with
  | none => shards=[]
  | some bs => ∃ es : List BufferEntry, bs = bufferedBytes es ∧ es.length < 256^4 ∧
      (∀ e ∈ es, BufferEntrySized e) ∧ EmptyBuffers es ∧ shards = es.map (·.1)

theorem bufferedShards_iff (v : Option Bytes) (shards : List Nat) :
    bufferedShards v = .ok shards ↔ BufferedValue v shards := by
  cases v with
  | none => simp [bufferedShards,BufferedValue,eq_comm]
  | some bs =>
    constructor
    · exact bufferedShards_inv
    · rintro ⟨es,rfl,hn,hs,he,rfl⟩
      exact bufferedShards_encode es hn hs he

end ZkFormal.NearV3.Qv
