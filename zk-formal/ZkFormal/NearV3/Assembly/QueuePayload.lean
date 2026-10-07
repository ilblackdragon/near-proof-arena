import ZkFormal.NearV3.Assembly.QueueForest
import ZkFormal.NearV3.Qv.Candidates.RecordTraffic

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv
open Qv.Candidates.ValueGen

/-- Concrete parser payload; accepted modes prove that the fallback is unused. -/
def queuePayload (mode : ParseMode) (bytes : Bytes) : Payload :=
  match mode with
  | .empty => .empty (bytes.take 8)
  | .buffered _ =>
    match pVec "shard_buffers" bufferEntryParser bytes with
    | .ok (es,_) => .buffer (es.map byteBufferOfEntry)
    | .error _ => .buffer []
  | .raw => .raw bytes

def queueRecord (p : QueueProvider) : Record :=
  ⟨p.vid,p.tau,p.users,queuePayload p.mode p.bytes⟩

private theorem byteBufferEntries_bytes (es : List BufferEntry) (he : EmptyBuffers es) :
    byteBufferedBytes (es.map byteBufferOfEntry) = bufferedBytes es := by
  unfold byteBufferedBytes bufferedBytes encList
  simp only [List.length_map,List.map_map]
  congr 2
  apply List.map_congr_left
  intro e hm
  exact byteBufferOfEntry_bytes e (he e hm)

theorem queueRecord_valid_bytes (p : QueueProvider)
    (hm : p.mode.Accepts (some p.bytes)) (hb : p.bytes.length ≤ B0) :
    (queueRecord p).Valid ∧ (queueRecord p).bytes = p.bytes := by
  cases p with
  | mk tau vid bytes mode users =>
    cases mode with
    | raw => exact ⟨trivial,rfl⟩
    | empty =>
      obtain ⟨ix,hix,rfl⟩ := (emptyQueue_some_iff bytes).mp hm
      simp only [queueRecord,queuePayload,Record.Valid,Record.bytes]
      have ht : (ix++ix).take 8=ix := by rw [←hix,List.take_left]
      simp only [ht,hix,true_and]
    | buffered shards =>
      obtain ⟨es,rfl,hn,hs,he,hshards⟩ := hm
      have hd := pVec_ok "shard_buffers" bufferEntryParser bufferEntryBytes es [] hn
        (fun e he rest => bufferEntryParser_encode e (hs e he) rest)
      simp only [List.append_nil] at hd
      change pVec "shard_buffers" bufferEntryParser (bufferedBytes es) = .ok (es,[]) at hd
      simp only [queueRecord,queuePayload,hd,Record.Valid,Record.bytes]
      refine ⟨⟨?_,?_⟩,byteBufferEntries_bytes es he⟩
      · intro e he
        obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
        exact byteBufferOfEntry_sized e
      · simp only [bufferedBytes_length,B0] at hb
        simp only [List.length_map]
        omega

def queueRecords (ps : List QueueProvider) : List Record := ps.map queueRecord

theorem queueRecords_valid_bytes (ps : List QueueProvider)
    (hm : ∀ p ∈ ps, p.mode.Accepts (some p.bytes))
    (hb : (ps.map (fun p => p.bytes.length)).sum ≤ B0) :
    (∀ r ∈ queueRecords ps, r.Valid) ∧
      ((queueRecords ps).map (fun r => r.bytes.length)).sum =
        (ps.map (fun p => p.bytes.length)).sum := by
  have hp : ∀ p ∈ ps, (queueRecord p).Valid ∧ (queueRecord p).bytes=p.bytes := by
    intro p hmem
    have hl := Link3.le_sum_mem (List.mem_map.mpr ⟨p,hmem,rfl⟩ : p.bytes.length ∈ ps.map (fun p => p.bytes.length))
    exact queueRecord_valid_bytes p (hm p hmem) (Nat.le_trans hl hb)
  constructor
  · intro r hr
    obtain ⟨p,hmem,rfl⟩ := List.mem_map.mp hr
    exact (hp p hmem).1
  · simp only [queueRecords,List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hmem
    exact congrArg List.length (hp p hmem).2

theorem checkD0a_queue_record_count {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre) :
    (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v
      (steps.map ImplicitStepV3.pre)))).length ≤ 83367 := by
  have hb : (v.buffered.map List.length).getD 0 ≤ B0 := by
    cases he : v.buffered with
    | none => simp [he,B0]
    | some b =>
      have hf := hreads.2.1
      rw [he] at hf
      have hh := checkD0a_read_bound hk hw h hm hv (by simp : m.pre ∈ m.pre :: steps.map ImplicitStepV3.pre) hf
      simpa only [he,Option.map_some,Option.getD_some] using hh
  have hshards := main_group_count_bound v hvalid hb
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,hK⟩ := checkD0_native_steps hk hw hc
  have hlen := hv.length
  simp only [List.length_zip] at hlen
  have hs : steps.length ≤ 31 := by omega
  have hn := queueForestProviders_length (queueInputs m.pre v (steps.map ImplicitStepV3.pre)) 0 0
  rw [queueInputs_request_count] at hn
  simp only [List.length_map] at hn
  simp only [queueRecords,List.length_map]
  unfold B0 at hshards
  omega

theorem checkD0a_queue_records {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      let ps := queueForestProviders 0 0 (queueInputs m.pre v (steps.map ImplicitStepV3.pre))
      (∀ r ∈ queueRecords ps, r.Valid) ∧
      ((queueRecords ps).map (fun r => r.bytes.length)).sum ≤ 2^21 ∧
      (queueRecords ps).length ≤ 83367 := by
  obtain ⟨v,hvalid,hreads,hh,hmode⟩ := native_queueInputs hm hv
  have hp := queueForestProviders_accepts _ 0 0 hh
  have hb := checkD0a_queue_provider_bytes hk hw h hm hv v
  obtain ⟨hr,he⟩ := queueRecords_valid_bytes _ hp hb
  refine ⟨v,hvalid,hreads,hr,?_,checkD0a_queue_record_count hk hw h hm hv v hvalid hreads⟩
  rw [he]
  have hB : B0 ≤ 2^21 := by decide
  exact Nat.le_trans hb hB

end ZkFormal.NearV3.Assembly
