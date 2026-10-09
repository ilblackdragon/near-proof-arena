import ZkFormal.NearV3.Render.Ups.TreeViewBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render

def seedValueId (s : NodeS3) : Option Nat := s.v.value.map (·.1)

mutual
theorem seedNodesT_valueIds (tau : Nat) : ∀ d n v t,
    (seedNodesT tau d n v t).filterMap seedValueId=List.range' v (valsOf t).length
  | _,_,v,.hash _ => by simp [seedNodesT,valsOf,occs]
  | d,n,v,.leaf k s m => by
    cases s <;> simp [seedNodesT,List.filterMap_cons,seedValueId,seedNodeView,viewNode,viewSlot,NodeV3.value,
      valsOf_leaf,slotVal,List.range'_succ]
  | d,n,v,.ext k c m => by
    simp [seedNodesT,List.filterMap_cons,seedValueId,seedNodeView,viewNode,NodeV3.value,valsOf_ext,
      seedNodesT_valueIds tau (d+1) (n+1) v c]
  | d,n,v,.branch sv cs m => by
    have ih := seedKidsT_valueIds tau (d+1) (n+1) (v+(optSlotVal sv).length) cs
    cases sv with
    | none => simpa [seedNodesT,List.filterMap_cons,seedValueId,seedNodeView,viewNode,NodeV3.value,valsOf_branch,optSlotVal] using ih
    | some s =>
      cases s <;> simp [seedNodesT,List.filterMap_cons,seedValueId,seedNodeView,viewNode,viewSlot,NodeV3.value,
        valsOf_branch,optSlotVal,slotVal,List.range'_succ] at ih ⊢ <;> exact ih
theorem seedKidsT_valueIds (tau : Nat) : ∀ d n v cs,
    (seedKidsT tau d n v cs).filterMap seedValueId=List.range' v (kvals cs).length
  | _,_,v,.nil => by simp [seedKidsT,kvals_nil]
  | d,n,v,.none rest => by simpa [seedKidsT,kvals_none] using seedKidsT_valueIds tau d n v rest
  | d,n,v,.some c rest => by
    simp [seedKidsT,kvals_some,seedNodesT_valueIds tau d n v c,
      seedKidsT_valueIds tau d (n+tsize c) (v+(valsOf c).length) rest,List.range'_append]
end

mutual
theorem seedNodesT_tau (tau : Nat) : ∀ d n v t s, s∈seedNodesT tau d n v t → s.tau=tau
  | _,_,_,.hash _,_,h => by simp [seedNodesT] at h
  | d,n,v,.leaf k value m,s,h => by
    simp only [seedNodesT,List.mem_singleton] at h
    subst s; rfl
  | d,n,v,.ext k c m,s,h => by
    simp only [seedNodesT,List.mem_cons] at h
    rcases h with rfl|h
    rfl
    exact seedNodesT_tau tau (d+1) (n+1) v c s h
  | d,n,v,.branch sv cs m,s,h => by
    simp only [seedNodesT,List.mem_cons] at h
    rcases h with rfl|h
    rfl
    exact seedKidsT_tau tau (d+1) (n+1) (v+(optSlotVal sv).length) cs s h
theorem seedKidsT_tau (tau : Nat) : ∀ d n v cs s, s∈seedKidsT tau d n v cs → s.tau=tau
  | _,_,_,.nil,_,h => by simp [seedKidsT] at h
  | d,n,v,.none rest,s,h => seedKidsT_tau tau d n v rest s h
  | d,n,v,.some c rest,s,h => by
    simp only [seedKidsT,List.mem_append] at h
    rcases h with h|h
    exact seedNodesT_tau tau d n v c s h
    exact seedKidsT_tau tau d (n+tsize c) (v+(valsOf c).length) rest s h
end

theorem valTau_of_valueId (nodes : List NodeS3) (tau i : Nat)
    (ht : ∀ s∈nodes,s.tau=tau) (hi : i∈nodes.filterMap seedValueId) : Link3.valTau nodes i=tau := by
  obtain ⟨s,hs,hi⟩ := List.mem_filterMap.mp hi
  have hp : (match s.v.value with | some (j,_) => j==i | none => false)=true := by
    cases hv : s.v.value with
    | none => simp [seedValueId,hv] at hi
    | some val => simp [seedValueId,hv] at hi; simp [hi]
  unfold Link3.valTau
  cases hf : nodes.find? (fun s => match s.v.value with | some (j,_) => j==i | none => false) with
  | none => exact False.elim (by have hn := List.find?_eq_none.mp hf s hs; simp [hp] at hn)
  | some found => simp [ht found (List.mem_of_find?_eq_some hf)]

/-- Every allocated value occurrence has a source node in the same instance. -/
theorem seedNodesT_valTau (tau d n v : Nat) (t : PTrie) (i : Nat)
    (hi : i∈List.range' v (valsOf t).length) : Link3.valTau (seedNodesT tau d n v t) i=tau := by
  apply valTau_of_valueId _ tau i (seedNodesT_tau tau d n v t)
  rwa [seedNodesT_valueIds]

def seedValue (vid : Nat) (bytes : Bytes) : ValE := {
  vid := vid, len := bytes.length, vz := bytes.isEmpty, dup := false,
  hd := false, repE := 0, bytes := bytes.map UInt8.toNat }

def seedValuesFrom : Nat → List Bytes → List ValE
  | _,[] => []
  | vid,bytes::rest => seedValue vid bytes::seedValuesFrom (vid+1) rest

theorem seedValuesFrom_records (nodes : List NodeS3) (tau : Nat) : ∀ vid bytes,
    (∀ i∈List.range' vid bytes.length,Link3.valTau nodes i=tau) →
    Link3.valsOf3 nodes (seedValuesFrom vid bytes)=bytes.map (ValRec3.mk tau)
  | _,[],_ => rfl
  | vid,bytes::rest,ht => by
    have hv := ht vid (by simp [List.range'_succ])
    have ihr := seedValuesFrom_records nodes tau (vid+1) rest
      (fun i hi => ht i (by simp only [List.length_cons,List.range'_succ,List.mem_cons]; exact Or.inr hi))
    simp only [seedValuesFrom,Link3.valsOf3,List.map_cons,seedValue,hv] at ihr ⊢
    rw [ihr]
    simp [Link3.toB,List.map_map,Function.comp_def]

/-- The actual value views extract to exactly the occurrence allocator's values. -/
theorem seedValuesT_records (tau : Nat) (t : PTrie) :
    Link3.valsOf3 (seedNodesT tau 0 0 0 t) (seedValuesFrom 0 (valsOf t))=valsT tau t := by
  exact seedValuesFrom_records _ tau 0 (valsOf t) (seedNodesT_valTau tau 0 0 0 t)

/-- Both lists are actual renderer views; their linked records reconstruct the input tree. -/
theorem seedViews_fullTree (tau : Nat) (t : PTrie) (hw : t.wf=true) (hn : isNode t=true) :
    fullTree (Link3.recsOf id (seedNodesT tau 0 0 0 t))
      (Link3.valsOf3 (seedNodesT tau 0 0 0 t) (seedValuesFrom 0 (valsOf t))) 0=t := by
  rw [seedValuesT_records]
  exact seedNodesT_fullTree tau t hw hn

theorem seedViews_store (tau : Nat) (t : PTrie) (hw : t.wf=true) (hn : isNode t=true) :
    storeOf (Link3.recsOf id (seedNodesT tau 0 0 0 t))
      (Link3.valsOf3 (seedNodesT tau 0 0 0 t) (seedValuesFrom 0 (valsOf t))) tau=
        (occs t).map nodeEnc++valsOf t := by
  rw [seedValuesT_records]
  exact seedNodesT_store tau t hw hn

end ZkFormal.NearV3.Render.UpsGen
