import ZkFormal.NearV3.Candidates.NativeQueuePartition

namespace ZkFormal.NearV3.Candidates.NativeQueuePhysicalBytes
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen

theorem numbered_eq (id off : Nat) (bytes : Bytes) :
    numberedBytes id off bytes=emitAt id off (bytes.map UInt8.toNat) := by
  apply List.ext_getElem (by simp [numberedBytes,emitAt])
  intro i hi hj
  have hib : i<bytes.length := by simpa [numberedBytes] using hi
  simp [numberedBytes,emitAt,hib,List.getD_eq_getElem?_getD]

/-- Exact queue physical byte sends, not merely inclusion in forest demand. -/
theorem physical_inventory {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (f : Resolve) (log : Nat) (pub msg : List Fp)
    (ha : ∀p∈queueForestProviders 0 0 (queueInputs pre v pres),p.mode.Accepts (some p.bytes))
    (hb : ((queueForestProviders 0 0 (queueInputs pre v pres)).map (fun p=>p.bytes.length)).sum≤B0)
    (hr : ∀r∈queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)),r.Valid)
    (hfit : ((plan pre v pres f).flatMap Walk.rows).length+
      recordsSize (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)))≤2^log) :
    tableBusCount CombinedTable.interactions
      (mixedTrace (plan pre v pres f) (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))) log)
      0 pub B_VBYTES true msg =
    cnt ((queueForestProviders 0 0 (queueInputs pre v pres)).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg := by
  have hs := mixedTrace_all_messages _ _ hr (plan_group_slot pre v pres f) log pub B_VBYTES true hfit
  simp only [mixedTraffic,Walk.wordMessages,canonicalTraffic,
    show B_VBYTES≠ValueTable.B_QVC by decide,show B_VBYTES≠B_KEYNIB by decide,
    ite_true,ite_false] at hs
  have hz : (plan pre v pres f).flatMap (fun _=>([] : List Msg))=[] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _=>rfl)
  rw [hz,List.nil_append,queueRecords_byte_list _ ha hb] at hs
  simp only [numbered_eq] at hs
  have he := hs.count_eq msg
  rw [ZkFormal.Near.tableBusCount_eq]
  simpa only [Trace.height,mixedTrace,cnt] using he

/-- SAME accepted execution supplies every validity and capacity condition. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre) (pub msg : List Fp) :
    let pres := steps.map ImplicitStepV3.pre
    tableBusCount CombinedTable.interactions
      (mixedTrace (plan m.pre v pres (NativeQueueIds.resolve m.pre v pres))
        (queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))) 22)
      0 pub B_VBYTES true msg =
    cnt ((queueForestProviders 0 0 (queueInputs m.pre v pres)).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg := by
  obtain ⟨hr,hfit⟩ := NativeQueueCounters.accepted_records hk hw hc hm hv v hvalid hreads
  exact physical_inventory _ _ 22 pub msg
    (queueForestProviders_accepts _ 0 0 (NativeQueueLookupBinding.native_holds hv v hvalid hreads))
    (checkD0a_queue_provider_bytes hk hw hc hm hv v) hr hfit

/-- Split exact forest provider traffic into original and implicit-state
parts, retaining the original occurrence offset of every implicit value. -/
theorem forest_split (pre : PTrie) (v : MainValues) (pres : List PTrie) (msg : List Fp) :
    cnt ((queueForestProviders 0 0 (queueInputs pre v pres)).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg =
    cnt ((queueProviders pre (mainRequests pre v) 0 0).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg+
    cnt ((queueForestProviders 1 (NearSpecV3.valsOf pre).length
      (pres.map (fun t=>(t,[missingRequest t])))).flatMap
      (fun p=>emitAt p.vid 0 (p.bytes.map UInt8.toNat))) msg := by
  simp only [queueInputs,queueForestProviders,Nat.zero_add,List.flatMap_append,
    cnt,List.map_append,List.count_append]

end ZkFormal.NearV3.Candidates.NativeQueuePhysicalBytes
