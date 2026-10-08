import ZkFormal.NearV3.Rcpt.Candidates.NodePairedForest
import ZkFormal.NearV3.Candidates.CombinedStoreOccurrences
namespace ZkFormal.NearV3.Candidates.PairedStoreKeys
open NearSpec ZkFormal.Near Render.UpsGen Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate
mutual
theorem nodes_keys : ∀(tau d n v : Nat){a b : PTrie},WriteTreePair a b →
    (pairedNodes tau d n v a b).map StoreDuplicateMetadata.nodeKey=
      (seedNodesT tau d n v a).map StoreDuplicateMetadata.nodeKey
  | _,_,_,_,_,_,.hash _ => rfl
  | tau,d,n,v,_,_,.leaf k m h => by
    simp only [pairedNodes,seedNodesT,List.map_cons,List.map_nil,pairedRecord,seedNodeView,StoreDuplicateMetadata.nodeKey]
    rw [pairedNode_pre n v (.leaf k m h)]
  | tau,d,n,v,_,_,.ext k m h => by
    simp only [pairedNodes,seedNodesT,List.map_cons,pairedRecord,seedNodeView,StoreDuplicateMetadata.nodeKey]
    rw [pairedNode_pre n v (.ext k m h),nodes_keys tau (d+1) (n+1) v h]
  | tau,d,n,v,_,_,.branch m h hs => by
    simp only [pairedNodes,seedNodesT,List.map_cons,pairedRecord,seedNodeView,StoreDuplicateMetadata.nodeKey]
    rw [pairedNode_pre n v (.branch m h hs),children_keys tau (d+1) (n+1) _ hs]
theorem children_keys : ∀(tau d n v : Nat){a b : Kids},WriteKidsPair a b →
    (pairedChildNodes tau d n v a b).map StoreDuplicateMetadata.nodeKey=
      (seedKidsT tau d n v a).map StoreDuplicateMetadata.nodeKey
  | _,_,_,_,_,_,.nil => rfl
  | tau,d,n,v,_,_,.none h => by simpa only [pairedChildNodes,seedKidsT] using children_keys tau d n v h
  | tau,d,n,v,_,_,.some h hs => by
    simp only [pairedChildNodes,seedKidsT,List.map_append]
    rw [nodes_keys tau d n v h,children_keys tau d _ _ hs]
end

theorem forest_keys : ∀(tau n v : Nat)(pairs : List (PTrie×PTrie)),
    (∀p∈pairs,WriteTreePair p.1 p.2) →
    (pairedForest tau n v pairs).map StoreDuplicateMetadata.nodeKey=
      (forestNodes tau n v (pairs.map Prod.fst)).map StoreDuplicateMetadata.nodeKey
  | _,_,_,[],_ => rfl
  | tau,n,v,(pre,post)::rest,h => by
    simp only [pairedForest,forestNodes,List.map_cons,List.map_append]
    rw [nodes_keys tau 0 n v (h (pre,post) (by simp))]
    rw [forest_keys _ _ _ rest (fun p hp => h p (by simp [hp]))]

theorem occurrences_of_keys {vs ws : List NodeS3}
    (h : vs.map StoreDuplicateMetadata.nodeKey=ws.map StoreDuplicateMetadata.nodeKey)
    (tau : ValE→Nat) (es : List ValE) :
    CombinedStoreOccurrences.allOccurrences vs tau es=CombinedStoreOccurrences.allOccurrences ws tau es := by
  have hh:=congrArg (fun ks : List HonestStoreRepresentatives.Key=>
    ks.zipIdx.map fun p=>(⟨p.1,eidN p.2⟩ : StoreDuplicateMetadata.Occurrence)) h
  unfold CombinedStoreOccurrences.allOccurrences
  congr 1
  simpa only [CombinedStoreOccurrences.nodeOccurrences,List.zipIdx_map,List.map_map,Function.comp_def,Prod.map,id] using hh

/-- Paired post payloads retain identical prestate duplicate classes and entity
IDs, so the original native witness still pays the same selected records. -/
theorem forest_occurrences (pairs : List (PTrie×PTrie))
    (hp : ∀p∈pairs,WriteTreePair p.1 p.2) (tau : ValE→Nat) (es : List ValE) :
    CombinedStoreOccurrences.allOccurrences (pairedForest 0 0 0 pairs) tau es=
      CombinedStoreOccurrences.allOccurrences (forestNodes 0 0 0 (pairs.map Prod.fst)) tau es :=
  occurrences_of_keys (forest_keys 0 0 0 pairs hp) tau es

end ZkFormal.NearV3.Candidates.PairedStoreKeys
