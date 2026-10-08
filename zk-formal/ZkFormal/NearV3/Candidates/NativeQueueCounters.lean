import ZkFormal.NearV3.Candidates.NativeQueueLookupBinding
import ZkFormal.NearV3.Assembly.QueuePhysicalBalance
import ZkFormal.NearV3.Assembly.QueueCapacity
import ZkFormal.NearV3.Qv.Candidates.CombinedPrepared

namespace ZkFormal.NearV3.Candidates.NativeQueueCounters
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen Rcpt.Candidates.NodePostUpdate
open Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen

/-- The recursive provider allocator and the lookup allocator use identical
forest offsets and prefix-use counters, including out-of-range requests. -/
theorem forest_resolve (xs : List (PTrie × List ReadRequest)) (base tau slot : Nat) :
    queueForestRankResolve xs base tau slot =
      let input := xs.getD tau (.hash [],[])
      let request := input.2.getD slot ⟨[],none,.raw⟩
      ((valueIndex input.1 request.key).map (fun i =>
        (base+(forestBytes ((xs.take tau).map Prod.fst)).length+i,
         queueUsers input.1 (input.2.take slot) i))).getD (0,0) := by
  induction xs generalizing base tau with
  | nil => simp [queueForestRankResolve, List.getD, valueIndex]
  | cons x xs ih =>
    rcases x with ⟨tree,rs⟩
    cases tau with
    | zero => simp [queueForestRankResolve,queueRankResolve,forestBytes]
    | succ tau =>
      simpa [queueForestRankResolve,List.getD,List.take_succ_cons,forestBytes,
        List.length_append,Nat.add_assoc,native_valsOf_eq] using ih (base+(NearSpecV3.valsOf tree).length) tau

theorem resolve_eq (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    NativeQueueIds.resolve pre v pres=queueForestRankResolve (queueInputs pre v pres) 0 := by
  funext tau slot
  rw [forest_resolve]
  simp only [NativeQueueIds.resolve,Nat.zero_add]
  have h : ((queueInputs pre v pres).take tau).map Prod.fst=(pre::pres).take tau := by
    rw [List.map_take]
    simp [queueInputs,List.map_map,Function.comp_def]
  rw [h]

/-- Actual queue lookup identities now share the complete physical counter
balance theorem, with the same trace on both sides. -/
theorem physical_balance {pre : PTrie} {v : MainValues} (pres : List PTrie)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    (log : Nat) (pub : List Fp)
    (hv : ∀ r ∈ queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)), r.Valid)
    (hfit : ((plan pre v pres (NativeQueueIds.resolve pre v pres)).flatMap Walk.rows).length+
      recordsSize (queueRecords (queueForestProviders 0 0 (queueInputs pre v pres)))≤2^log) :
    let ws := plan pre v pres (NativeQueueIds.resolve pre v pres)
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs pre v pres))
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC true)).Perm
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC false)) := by
  rw [resolve_eq] at hfit ⊢
  exact plan_physical_qvc_balance pres hh log pub hv hfit

/-- Capacity and parser validity for the SAME MainValues used by the shared
native allocation, without choosing a second execution witness. -/
theorem accepted_records {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre) :
    let pres := steps.map ImplicitStepV3.pre
    let records := queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    (∀ r ∈ records, r.Valid) ∧
      ((plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)).flatMap Walk.rows).length+
        recordsSize records ≤ 2^22 := by
  have hh := NativeQueueLookupBinding.native_holds hv v hvalid hreads
  have hp := queueForestProviders_accepts _ 0 0 hh
  have hb := checkD0a_queue_provider_bytes hk hw hc hm hv v
  obtain ⟨hr,he⟩ := queueRecords_valid_bytes _ hp hb
  have hbytes : ((queueRecords (queueForestProviders 0 0
      (queueInputs m.pre v (steps.map ImplicitStepV3.pre)))).map (fun r => r.bytes.length)).sum ≤ 2^21 := by
    rw [he]
    exact Nat.le_trans hb (by decide : B0 ≤ 2^21)
  have hcount := checkD0a_queue_record_count hk hw hc hm hv v hvalid hreads
  have hbuffer : (v.buffered.map List.length).getD 0 ≤ 3000000 := by
    cases he : v.buffered with
    | none => simp [he]
    | some b =>
      have hf := hreads.2.1
      rw [he] at hf
      have hh := checkD0a_read_bound hk hw hc hm hv
        (by simp : m.pre ∈ m.pre :: steps.map ImplicitStepV3.pre) hf
      simpa only [he,Option.map_some,Option.getD_some] using
        Nat.le_trans hh (by decide : B0 ≤ 3000000)
  have hcheck := hc
  unfold checkD0a at hcheck
  obtain ⟨u,hcheck,_⟩ := ReexecV3D0.bind_ok' hcheck
  cases u
  obtain ⟨_,_,_,_,hcnt,hK⟩ := checkD0_native_steps hk hw hcheck
  have hlen := hv.length
  simp only [List.length_zip] at hlen
  have hs : (steps.map ImplicitStepV3.pre).length ≤ 31 := by simp only [List.length_map]; omega
  exact ⟨hr,combined_rows_fit m.pre v _ _ hvalid hbuffer hs _ hr hbytes (by omega)⟩

/-- Construct the actual log-22 queue table with local constraints, its full
traffic specification and physical QVC conservation from accepted native input.
The remaining global byte ownership and other bus joins are separate obligations. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hc : checkD0a B0 cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (v : MainValues) (hvalid : v.Valid) (hreads : v.Reads m.pre m.pre m.pre)
    (d : Walk) (p : Prep) (overhead : Nat)
    (hroots : Public.RootsSized p) (hK : p.hdr.K<256^4) (hcount : steps.length=p.hdr.K) :
    let pres := steps.map ImplicitStepV3.pre
    let ws := plan m.pre v pres (NativeQueueIds.resolve m.pre v pres)
    let vs := queueRecords (queueForestProviders 0 0 (queueInputs m.pre v pres))
    let tr := mixedTrace ws vs 22
    let pub := ZkFormal.Udr.pubOf Fp (Public.preparedBytes p overhead)
    TableLocal CombinedTable.table tr 0 pub ∧
    TableTraffic CombinedTable.interactions tr 0 pub (mixedTraffic ws vs) ∧
    ((List.range (2^22)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions tr 0 r pub ValueTable.B_QVC true)).Perm
    ((List.range (2^22)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions tr 0 r pub ValueTable.B_QVC false)) := by
  obtain ⟨hr,hfit⟩ := accepted_records hk hw hc hm hv v hvalid hreads
  have hlocal := plan_prepared_local_and_traffic m.pre v (steps.map ImplicitStepV3.pre)
    (NativeQueueIds.resolve m.pre v (steps.map ImplicitStepV3.pre)) hvalid d _ hr 22 p overhead
    (by decide) hfit hroots hK (by simpa using hcount)
  exact ⟨hlocal.1,hlocal.2,physical_balance _
    (NativeQueueLookupBinding.native_holds hv v hvalid hreads) 22 _ hr hfit⟩

end ZkFormal.NearV3.Candidates.NativeQueueCounters
