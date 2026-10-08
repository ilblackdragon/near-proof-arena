import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestDepth
import ZkFormal.NearV3.Assembly.ForestNodeBytes

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render.UpsGen

/-- Initial local metadata, in the same global node order as the forest. -/
def initializeList : Nat→List NodeS3→List NodeS3
  | _,[] => []
  | n,s::ss => initializeMetadata n s::initializeList (n+1) ss

theorem initializeList_length (n : Nat) (ss : List NodeS3) :
    (initializeList n ss).length=ss.length := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [initializeList,ih]

theorem initializeList_member : ∀(ss : List NodeS3)(n : Nat)(s : NodeS3),
    s∈initializeList n ss → ∃i∈List.range ss.length,∃o,ss[i]?=some o ∧ s=initializeMetadata (n+i) o
  | [],_,_,h => by simp [initializeList] at h
  | o::ss,n,s,h => by
    simp only [initializeList,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨0,by simp,o,rfl,by simp⟩
    · obtain ⟨i,hi,o,ho,he⟩:=initializeList_member ss (n+1) s h
      refine ⟨i+1,by simpa using hi,o,by simpa using ho,?_⟩
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he

theorem initializeList_get : ∀(ss : List NodeS3)(n i : Nat),
    (initializeList n ss)[i]?=ss[i]?.map (initializeMetadata (n+i))
  | [],_,_ => by simp [initializeList]
  | s::ss,n,0 => by simp [initializeList]
  | s::ss,n,i+1 => by
    simpa [initializeList,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using initializeList_get ss (n+1) i

theorem initializeList_bytes (ss : List NodeS3) (n : Nat) :
    (initializeList n ss).map (fun s=>(s.v.ser false).length)=ss.map (fun s=>(s.v.ser false).length) := by
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih => simp [initializeList,initializeMetadata,ih]

/-- The initializer supplies every local metadata obligation; traffic use counts
are zero and must subsequently be assigned by the global ownership construction. -/
theorem initializeList_wf (ss : List NodeS3)
    (hw : ∀s∈ss,s.v.wf)
    (hd : ∀s∈ss,s.depth<400)
    (hr : ∀(i : Nat)(s : NodeS3),ss[i]?=some s → s.resOk i)
    (hs : ∀s∈ss,s.tau<P ∧ s.res<P ∧ s.ubm<P ∧ s.repE<P)
    (hc : ∀s∈ss,∀x∈s.v.raw,x<P)
    (hn : ss.length≤2^22)
    (hb : (ss.map (fun s=>(s.v.ser false).length)).sum+1≤2^22) :
    NodeWf3 (initializeList 0 ss) := by
  have hm : ∀s∈initializeList 0 ss,∃i o,ss[i]?=some o ∧ o∈ss ∧ s=initializeMetadata i o := by
    intro s h
    obtain ⟨i,_,o,ho,he⟩:=initializeList_member ss 0 s h
    exact ⟨i,o,ho,List.mem_of_getElem? ho,by simpa using he⟩
  have hg : ∀i (h : i<(initializeList 0 ss).length),
      ∃o,ss[i]?=some o ∧ (initializeList 0 ss)[i]=initializeMetadata i o := by
    intro i h
    have hget:=initializeList_get ss 0 i
    rw [List.getElem?_eq_getElem h] at hget
    cases ho : ss[i]? with
    | none => simp [ho] at hget
    | some o => exact ⟨o,rfl,by simpa [ho] using hget⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h;exact hw o ho
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h;exact Or.inl (hd o ho)
  · intro i hi;obtain ⟨o,ho,he⟩:=hg i hi;rw [he];exact hr i o ho
  · intro i hi;obtain ⟨o,ho,he⟩:=hg i hi;rw [he]
    exact (initializeMetadata_arrays i o (hw o (List.mem_of_getElem? ho))).1
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h
    obtain ⟨ht,hr,hu,he⟩:=hs o ho
    have hdepth:=hd o ho
    exact ⟨ht,by change o.depth<2013265921;omega,hr,hu,he,
      (initializeMetadata_small i o (hc o ho)).1⟩
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h;exact hc o ho
  · simpa [initializeList_length] using hn
  · simpa [initializeList_bytes] using hb
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h
    exact ⟨(initializeMetadata_arrays i o (hw o ho)).2.1,
      (initializeMetadata_arrays i o (hw o ho)).2.2.1⟩
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h
    exact (initializeMetadata_small i o (hc o ho)).2
  · intro s h;obtain ⟨i,o,_,ho,rfl⟩:=hm s h;exact windowIds_kidCid o.v

theorem forest_length : ∀(ts : List PTrie)(tau n v : Nat),
    (Assembly.forestNodes tau n v ts).length=(ts.flatMap occs).length
  | [],_,_,_ => rfl
  | t::ts,tau,n,v => by
    simp [Assembly.forestNodes,seedNodesT_length,forest_length ts,tsize]

/-- Full local validity of the concrete native occurrence forest, including all
metadata arrays. This does not assert global bus balance for the initial zero counts. -/
theorem native_forest_wf (ts : List PTrie)
    (hw : ∀t∈ts,t.wf=true) (hb : Assembly.preBytes ts≤2000000)
    (hf : ∀t∈ts,∀k,fdepth t k≤NearSpecV3.trieFuel)
    (ht : ts.length≤P) :
    NodeWf3 (initializeList 0 (Assembly.forestNodes 0 0 0 ts)) := by
  have hn:=forest_allocation_counts ts hb
  apply initializeList_wf
  · intro s hs
    obtain ⟨o,ho,tau,d,n,v,rfl,_,_,_⟩:=forest_allocation ts 0 0 0 s hs
    exact native_forest_node_wf ts hw hb n v o ho
  · exact native_forest_depth ts 0 0 0 hf
  · intro i s h
    simpa using forest_index_res ts 0 0 0 i s h
  · intro s hs
    obtain ⟨o,ho,tau,d,n,v,rfl,htau,hn',_⟩:=forest_allocation ts 0 0 0 s hs
    obtain ⟨t,_,ho⟩:=List.mem_flatMap.mp ho
    have hr:=target_bound o n (occs_isNode t o ho)
    refine ⟨by change tau<P;omega,?_,by change 0<P;decide,by change 0<P;decide⟩
    change viewTarget n o<2013265921
    omega
  · exact native_forest_canonical ts hw hb
  · rw [forest_length];omega
  · have hp:=Assembly.forestNodes_byte_charge ts hw
    omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
