import ZkFormal.NearV3.Candidates.NativeExecutionPost

namespace ZkFormal.NearV3.Candidates.NativePostShaBudget
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem node_lengths (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (cs : List StoreDuplicateChain.Entry) (u : Inputs) (q : UseRequests) :
    (assignList q 0 (records u (ChainMetadata.assign cs 0
      (initializeList 0 (forestNodes 0 0 0 ts))))).map (fun s=>(s.v.ser false).length)=
      (ts.flatMap occs).map (fun t=>(nodeEnc t).length) := by
  rw [assignList_bytes,records_pre_lengths,ChainMetadata.assign_bytes,initializeList_bytes]
  have h:=congrArg (fun xs : List (List Nat)=>xs.map List.length) (forestNodes_bytes false 0 0 0 ts hw)
  simpa only [List.map_map,Function.comp_def,List.length_map] using h

theorem value_lengths (cs : List StoreDuplicateChain.Entry) (n : Nat) (bs : List Bytes) :
    (ChainMetadata.assignValues cs (seedValuesFrom n bs)).map (fun v=>v.bytes.length)=bs.map List.length := by
  induction bs generalizing n with
  | nil => rfl
  | cons b bs ih => simpa [ChainMetadata.assignValues,ChainMetadata.patchValue,seedValuesFrom,seedValue] using congrArg (List.cons b.length) (ih (n+1))

/-- Actual updated, duplicate-accounted, usage-counted native node/value jobs
fit the established SHA budget. No abstract view length/wf premises remain. -/
theorem accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (hc : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (u : Inputs) (q : UseRequests) (he : q.edges.length<Algebra.P)
    (hb : q.bmaps.length<Algebra.P) (hu : q.windows.length<Algebra.P) :
    let ts:=m.pre::steps.map ImplicitStepV3.pre
    let vs:=initializeList 0 (forestNodes 0 0 0 ts)
    let es:=seedValuesFrom 0 (forestBytes ts)
    let cs:=StoreClassPartition.chain (CombinedStoreOccurrences.allOccurrences vs (NativeStoreProvenance.valueTau ts) es)
    let ns:=assignList q 0 (records u (ChainMetadata.assign cs 0 vs))
    let vals:=ChainMetadata.assignValues cs es
    ((nativeShaJobs ns vals).map (fun m=>Render.rowsOf m.bytes.length)).sum≤2925275 := by
  have hd : checkD0 cb wb=.ok () := by
    have hh:=((relD0a_iff B0 cb wb).mpr hc).1
    unfold RelD0 acceptsD0 at hh
    split at hh <;> simp_all
  obtain ⟨_,_,_,_,_,hcount⟩:=checkD0_native_steps hk hw hd
  have hs : steps.length≤31 := by
    have hh:=hv.length
    simp only [List.length_zip] at hh
    omega
  have hgood : ∀t∈m.pre::steps.map ImplicitStepV3.pre,t.wf=true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl|ht
    · rw [hm.pre];exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  have hn:=(NativeExecutionPost.assigned_inputs hk hw hc (by decide) hm hv u q he hb hu).1
  exact accepted_updated_nativeShaJobs hk hw hc hm hv hs hgood _ _ hn.wf
    (node_lengths _ hgood _ u q) (value_lengths _ _ _)

end ZkFormal.NearV3.Candidates.NativePostShaBudget
