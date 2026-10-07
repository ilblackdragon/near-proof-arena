import ZkFormal.NearV3.Assembly.QueueSeedSublist

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv Render.UpsGen Qv.Candidates.ValueGen
open ZkFormal.Near

def seedByteMessages (e : ValE) : List Msg :=
  if e.vz then [] else (List.range e.bytes.length).map (fun i => [e.vid,i,e.bytes.getD i 0])

theorem seedValue_bytes (vid : Nat) (bs : Bytes) :
    seedByteMessages (seedValue vid bs)=numberedBytes vid 0 bs := by
  by_cases hb : bs=[]
  · simp [hb,seedByteMessages,seedValue,numberedBytes]
  · have hv : bs.isEmpty=false := List.isEmpty_eq_false_iff.mpr hb
    simp only [seedByteMessages,seedValue,hv,Bool.false_eq_true,ite_false,List.length_map,numberedBytes]
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hib : i<bs.length := by simpa using hi
    simp [List.getD_eq_getElem?_getD,hib]

/-- Parser-selected bytes form a true sublist of seeded valV3 demand: no
 duplicate use is silently erased, and unrelated values remain unselected. -/
theorem queueForestProviders_byte_sublist (xs : List (PTrie × List ReadRequest)) :
    ((queueForestProviders 0 0 xs).flatMap (fun p => numberedBytes p.vid 0 p.bytes)).Sublist
      (valRecvs (forestStoreViews (xs.map Prod.fst)).values B_VBYTES) := by
  have h := sublist_flatMap seedByteMessages (queueForestProviders_seed_sublist xs 0 0)
  simp only [List.flatMap_map,Function.comp_def,seedValue_bytes] at h
  exact h

theorem queueRecords_byte_list (ps : List QueueProvider)
    (ha : ∀ p ∈ ps, p.mode.Accepts (some p.bytes))
    (hb : (ps.map (fun p => p.bytes.length)).sum≤B0) :
    (queueRecords ps).flatMap (fun r => numberedBytes r.vid 0 r.bytes)=
      ps.flatMap (fun p => numberedBytes p.vid 0 p.bytes) := by
  simp only [queueRecords,List.flatMap_map]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro p hp
  have hl := Link3.le_sum_mem (List.mem_map.mpr ⟨p,hp,rfl⟩ : p.bytes.length ∈ ps.map (fun p => p.bytes.length))
  rw [(queueRecord_valid_bytes p (ha p hp) (Nat.le_trans hl hb)).2]
  rfl

theorem queueRecords_byte_sublist (xs : List (PTrie × List ReadRequest))
    (ha : ∀ p ∈ queueForestProviders 0 0 xs, p.mode.Accepts (some p.bytes))
    (hb : ((queueForestProviders 0 0 xs).map (fun p => p.bytes.length)).sum≤B0) :
    ((queueRecords (queueForestProviders 0 0 xs)).flatMap (fun r => numberedBytes r.vid 0 r.bytes)).Sublist
      (valRecvs (forestStoreViews (xs.map Prod.fst)).values B_VBYTES) := by
  rw [queueRecords_byte_list _ ha hb]
  exact queueForestProviders_byte_sublist xs

theorem checkD0a_queue_bytes {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∃ v : MainValues, v.Valid ∧ v.Reads m.pre m.pre m.pre ∧
      ((queueRecords (queueForestProviders 0 0 (queueInputs m.pre v (steps.map ImplicitStepV3.pre)))).flatMap
        (fun r => numberedBytes r.vid 0 r.bytes)).Sublist
        (valRecvs (forestStoreViews (m.pre::steps.map ImplicitStepV3.pre)).values B_VBYTES) := by
  obtain ⟨v,hvalid,hreads,hh,hmode⟩ := native_queueInputs hm hv
  refine ⟨v,hvalid,hreads,?_⟩
  have ha := queueForestProviders_accepts _ 0 0 hh
  have hb := checkD0a_queue_provider_bytes hk hw h hm hv v
  simpa only [queueInputs_pre] using queueRecords_byte_sublist _ ha hb

open Qv.Candidates Qv.Candidates.CombinedWalkGen ZkFormal.Air ZkFormal.Algebra

/-- Physical parser bytes are a permutation of a sublist of the concrete
 seeded valV3 requests. Other byte suppliers remain separate. -/
theorem plan_physical_vbytes_inclusion {pre : PTrie} {v : MainValues} (pres : List PTrie) (resolve : Resolve)
    (ha : ∀ p ∈ queueForestProviders 0 0 (queueInputs pre v pres), p.mode.Accepts (some p.bytes))
    (hb : ((queueForestProviders 0 0 (queueInputs pre v pres)).map (fun p => p.bytes.length)).sum≤B0)
    (log : Nat) (pub : List Fp)
    (hv : ∀ r ∈ queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)), r.Valid)
    (hfit : ((plan pre v pres resolve).flatMap Walk.rows).length+
      recordsSize (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)))≤2^log) :
    let ws := plan pre v pres resolve
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    ∃ msgs, msgs.Sublist ((valRecvs (forestStoreViews (pre::pres)).values B_VBYTES).map Msg.toFp) ∧
      ((List.range (2^log)).flatMap (fun r =>
        rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_VBYTES true)).Perm msgs := by
  dsimp only
  refine ⟨((queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))).flatMap
    (fun r => numberedBytes r.vid 0 r.bytes)).map Msg.toFp,?_,?_⟩
  · have h := (queueRecords_byte_sublist (queueInputs pre v pres) ha hb).map Msg.toFp
    simpa only [queueInputs_pre] using h
  · have hs := mixedTrace_all_messages _ _ hv (plan_group_slot pre v pres resolve) log pub B_VBYTES true hfit
    simp only [mixedTraffic,Walk.wordMessages,canonicalTraffic,
      show B_VBYTES≠ValueTable.B_QVC by decide,show B_VBYTES≠B_KEYNIB by decide,
      ite_true,ite_false] at hs
    have hz : (plan pre v pres resolve).flatMap (fun _ => ([] : List Msg))=[] :=
      List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
    rw [hz,List.nil_append] at hs
    exact hs

end ZkFormal.NearV3.Assembly
