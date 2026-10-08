import ZkFormal.NearV3.Candidates.NativeStoreRepresentatives
import ZkFormal.NearV3.Candidates.StoreSelectedCharge
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestAllocation
namespace ZkFormal.NearV3.Candidates.NativeStoreProvenance
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3.Assembly Render.UpsGen
open Rcpt.Candidates.NodePostUpdate StoreDuplicateMetadata CombinedStoreOccurrences HonestStoreRepresentatives

def nativeKeys (tau : Nat) (ts : List PTrie) : List Key :=
  (ts.zipIdx tau).flatMap fun p=>(normalStore p.1).map fun b=>(p.2,b)

private theorem seed_key (tau d n v : Nat) (t : PTrie) (hw : t.wf=true)
    (s : NodeS3) (hs : s∈seedNodesT tau d n v t) :
    nodeKey s∈(normalStore t).map (fun b=>(tau,b)) := by
  obtain ⟨o,ho,d',n',v',rfl,_,_⟩:=seed_allocation t tau d n v s hs
  have hw':=occs_wf t hw o ho
  have hn:=occs_isNode t o ho
  have hb : nodeKey (seedNodeView tau d' n' v' o)=(tau,nodeEnc o) := by
    unfold nodeKey seedNodeView
    rw [viewNode_ser n' v' o hw' hn false]
    simp [toBytes,List.map_map,Function.comp_def]
  rw [hb]
  apply List.mem_map.mpr
  refine ⟨nodeEnc o,?_,rfl⟩
  simp only [normalStore,List.mem_eraseDups,List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨o,ho,rfl⟩)

theorem node_keys (ts : List PTrie) (tau n v : Nat) (hw : ∀t∈ts,t.wf=true) :
    (forestNodes tau n v ts).map nodeKey⊆nativeKeys tau ts := by
  induction ts generalizing tau n v with
  | nil => simp [forestNodes]
  | cons t ts ih =>
    intro key hk
    simp only [forestNodes,List.map_append,List.mem_append] at hk
    simp only [nativeKeys,List.zipIdx_cons,List.flatMap_cons]
    rcases hk with hk|hk
    · obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hk
      exact List.mem_append_left _ (seed_key tau 0 n v t (hw t (by simp)) s hs)
    · exact List.mem_append_right _ (ih _ _ _ (fun t ht=>hw t (by simp [ht])) hk)

theorem value_keys (ts : List PTrie) (tau : Nat) :
    (forestVals tau ts).map (fun r=>(r.tau,r.bytes))⊆nativeKeys tau ts := by
  induction ts generalizing tau with
  | nil => simp [forestVals]
  | cons t ts ih =>
    intro key hk
    simp only [forestVals,List.map_append,List.mem_append] at hk
    simp only [nativeKeys,List.zipIdx_cons,List.flatMap_cons]
    rcases hk with hk|hk
    · obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hk
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hr
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨b,List.mem_eraseDups.mpr (List.mem_append_right _ hb),rfl⟩
    · exact List.mem_append_right _ (ih _ hk)

def valueTau (ts : List PTrie) (e : ValE) : Nat :=
  Link3.valTau (forestNodes 0 0 0 ts) e.vid

/-- Every generated node/value byte key has the actual transition tag of its
native source tree. Value tags come from the allocated native parent slot. -/
theorem combined_keys (ts : List PTrie) (hw : ∀t∈ts,t.wf=true) :
    ((allOccurrences (forestNodes 0 0 0 ts) (valueTau ts) (seedValuesFrom 0 (forestBytes ts))).map
      Occurrence.key)⊆nativeKeys 0 ts := by
  intro key hk
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hk
  rcases List.mem_append.mp hr with hr|hr
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
    exact node_keys ts 0 0 0 hw (List.mem_map.mpr ⟨p.1,List.fst_mem_of_mem_zipIdx hp,rfl⟩)
  · have he : (valueOccurrences (valueTau ts) (seedValuesFrom 0 (forestBytes ts))).map Occurrence.key=
        (forestVals 0 ts).map (fun r=>(r.tau,r.bytes)) := by
      have h:=congrArg (List.map (fun r : ValRec3=>(r.tau,r.bytes))) (forestViews_values 0 0 0 ts)
      simpa [valueOccurrences,valueTau,Link3.valsOf3,Link3.toB,toBytes,List.map_map,Function.comp_def] using h
    apply value_keys ts 0
    rw [←he]
    exact List.mem_map.mpr ⟨r,hr,rfl⟩

/-- Honest combined AIR occurrences are covered by the actual native serialized
stores. This discharges the byte-provenance premise of selected-charge bounds. -/
theorem original_keys (ts : List PTrie) (store : Nat→List Bytes)
    (hw : ∀t∈ts,t.wf=true) (hs : ∀p∈ts.zipIdx,Stored (mkStore (store p.2)) p.1) :
    ((allOccurrences (forestNodes 0 0 0 ts) (valueTau ts) (seedValuesFrom 0 (forestBytes ts))).map
      Occurrence.key)⊆NativeStoreRepresentatives.originals ts store := by
  intro key hk
  exact NativeStoreRepresentatives.coverage ts store hs (combined_keys ts hw hk)
end ZkFormal.NearV3.Candidates.NativeStoreProvenance
