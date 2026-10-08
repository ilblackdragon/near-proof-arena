import ZkFormal.NearV3.Rcpt.Candidates.NativeForestByteBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen

mutual
theorem seed_allocation : ∀(t : PTrie)(tau d n v : Nat)(s : NodeS3),
    s∈seedNodesT tau d n v t → ∃o∈occs t,∃d' n' v',
    s=seedNodeView tau d' n' v' o ∧ n'+tsize o≤n+tsize t ∧
    v'+(valsOf o).length≤v+(valsOf t).length
  | .hash _,_,_,_,_,_,h => by simp [seedNodesT] at h
  | .leaf k sl m,tau,d,n,v,s,h => by
    simp only [seedNodesT,List.mem_singleton] at h
    exact ⟨_,by simp [occs],d,n,v,h,by omega,by omega⟩
  | .ext k c m,tau,d,n,v,s,h => by
    simp only [seedNodesT,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨_,by simp [occs],d,n,v,rfl,by omega,by omega⟩
    · obtain ⟨o,ho,d',n',v',he,hn,hv⟩:=seed_allocation c tau (d+1) (n+1) v s h
      refine ⟨o,by simp [occs,ho],d',n',v',he,?_,?_⟩
      · simp only [tsize,occs,List.length_cons] at *;omega
      · simpa [valsOf_ext] using hv
  | .branch sl cs m,tau,d,n,v,s,h => by
    simp only [seedNodesT,List.mem_cons] at h
    rcases h with rfl|h
    · exact ⟨_,by simp [occs],d,n,v,rfl,by omega,by omega⟩
    · obtain ⟨o,ho,d',n',v',he,hn,hv⟩:=seed_kid_allocation cs tau (d+1) (n+1) (v+(optSlotVal sl).length) s h
      refine ⟨o,by simp [occs,ho],d',n',v',he,?_,?_⟩
      · simp only [tsize,ksize,occs,List.length_cons] at *;omega
      · simpa [valsOf_branch,List.length_append,Nat.add_assoc] using hv
theorem seed_kid_allocation : ∀(cs : Kids)(tau d n v : Nat)(s : NodeS3),
    s∈seedKidsT tau d n v cs → ∃o∈kOccs cs,∃d' n' v',
    s=seedNodeView tau d' n' v' o ∧ n'+tsize o≤n+ksize cs ∧
    v'+(valsOf o).length≤v+(kvals cs).length
  | .nil,_,_,_,_,_,h => by simp [seedKidsT] at h
  | .none cs,tau,d,n,v,s,h => seed_kid_allocation cs tau d n v s h
  | .some c cs,tau,d,n,v,s,h => by
    simp only [seedKidsT,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨o,ho,d',n',v',he,hn,hv⟩:=seed_allocation c tau d n v s h
      refine ⟨o,by simp [kOccs,ho],d',n',v',he,?_,?_⟩
      · simp only [ksize,tsize,kOccs,List.length_append] at *;omega
      · simp only [kvals_some,List.length_append];omega
    · obtain ⟨o,ho,d',n',v',he,hn,hv⟩:=seed_kid_allocation cs tau d (n+tsize c) (v+(valsOf c).length) s h
      refine ⟨o,by simp [kOccs,ho],d',n',v',he,?_,?_⟩
      · simp only [ksize,tsize,kOccs,List.length_append] at *;omega
      · simp only [kvals_some,List.length_append];omega
end

theorem forest_allocation : ∀(ts : List PTrie)(tau n v : Nat)(s : NodeS3),
    s∈Assembly.forestNodes tau n v ts → ∃o∈ts.flatMap occs,∃tau' d' n' v',
    s=seedNodeView tau' d' n' v' o ∧ tau'<tau+ts.length ∧
    n'+tsize o≤n+(ts.flatMap occs).length ∧
    v'+(valsOf o).length≤v+(Assembly.forestBytes ts).length
  | [],_,_,_,_,h => by simp [Assembly.forestNodes] at h
  | t::ts,tau,n,v,s,h => by
    simp only [Assembly.forestNodes,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨o,ho,d',n',v',he,hn,hv⟩:=seed_allocation t tau 0 n v s h
      refine ⟨o,by simp [ho],tau,d',n',v',he,by simp,?_,?_⟩
      · simp only [List.flatMap_cons,List.length_append,tsize] at *;omega
      · simp only [Assembly.forestBytes,List.flatMap_cons,List.length_append];omega
    · obtain ⟨o,ho,tau',d',n',v',he,ht,hn,hv⟩:=forest_allocation ts (tau+1)
        (n+tsize t) (v+(valsOf t).length) s h
      refine ⟨o,by simp [ho],tau',d',n',v',he,?_,?_,?_⟩
      · simp only [List.length_cons];omega
      · simp only [List.flatMap_cons,List.length_append,tsize] at *;omega
      · simp only [Assembly.forestBytes,List.flatMap_cons,List.length_append] at *;omega

theorem forest_canonical (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000)
    (hn : (ts.flatMap occs).length≤ZkFormal.Algebra.P)
    (hv : (Assembly.forestBytes ts).length<ZkFormal.Algebra.P) :
    ∀s∈Assembly.forestNodes 0 0 0 ts,∀x∈s.v.raw,x<ZkFormal.Algebra.P := by
  intro s hs
  obtain ⟨o,ho,tau,d,n,v,rfl,_,hn',hv'⟩:=forest_allocation ts 0 0 0 s hs
  obtain ⟨t,ht,hot⟩:=List.mem_flatMap.mp ho
  apply native_node_canonical n v o (occs_wf t (hw t ht) o hot) (by omega) (by omega)
  · intro c hc
    exact native_forest_node_byte_bound ts hb c
      (List.mem_flatMap.mpr ⟨t,ht,occs_trans t o hot c hc⟩)
  · intro b hval
    obtain ⟨c,hc,hbval⟩:=List.mem_flatMap.mp hval
    have hroot:=ownVals_sub (occs_trans t o hot c hc) hbval
    exact native_forest_value_byte_bound ts hw hb b (List.mem_flatMap.mpr ⟨t,ht,hroot⟩)

theorem revealed_node_positive (t : PTrie) (h : isNode t=true) : 0<(nodeEnc t).length := by
  cases t with
  | hash _ => simp [isNode] at h
  | leaf k s m => simp [nodeEnc]
  | ext k c m => simp [nodeEnc]
  | branch sv cs m => cases sv <;> simp [nodeEnc]

theorem occurrence_count_le_bytes (os : List PTrie) (h : ∀o∈os,isNode o=true) :
    os.length≤(os.map (fun o => (nodeEnc o).length)).sum := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have hp:=revealed_node_positive o (h o (by simp))
    have ht:=ih (fun o ho=>h o (by simp [ho]))
    simp only [List.length_cons,List.map_cons,List.sum_cons];omega

theorem own_values_count (os : List PTrie) : (os.flatMap ownVals).length≤os.length := by
  induction os with
  | nil => simp
  | cons o os ih =>
    have ho : (ownVals o).length≤1 := by
      cases o with
      | hash _ => simp [ownVals]
      | ext k c m => simp [ownVals]
      | leaf k sl m => cases sl <;> simp [ownVals,optSlotVal,slotVal]
      | branch sv cs m => cases sv with
        | none => simp [ownVals,optSlotVal]
        | some sl => cases sl <;> simp [ownVals,optSlotVal,slotVal]
    simp only [List.flatMap_cons,List.length_append,List.length_cons];omega

theorem forest_allocation_counts (ts : List PTrie) (hb : Assembly.preBytes ts≤2000000) :
    (ts.flatMap occs).length≤2000000 ∧ (Assembly.forestBytes ts).length≤2000000 := by
  have hn:=occurrence_count_le_bytes (ts.flatMap occs) (by
    intro o ho;obtain ⟨t,_,ho⟩:=List.mem_flatMap.mp ho;exact occs_isNode t o ho)
  have hb':=node_occurrence_byte_sum ts
  have hv:=own_values_count (ts.flatMap occs)
  have he : Assembly.forestBytes ts=(ts.flatMap occs).flatMap ownVals := by
    rw [List.flatMap_assoc]
    rfl
  rw [he]
  omega

theorem native_forest_canonical (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (hb : Assembly.preBytes ts≤2000000) :
    ∀s∈Assembly.forestNodes 0 0 0 ts,∀x∈s.v.raw,x<ZkFormal.Algebra.P := by
  have hc:=forest_allocation_counts ts hb
  apply forest_canonical ts hw hb
  · change _≤2013265921;omega
  · change _<2013265921;omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
