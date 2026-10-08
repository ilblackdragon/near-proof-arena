import ZkFormal.NearV3.Rcpt.Candidates.NodePairedForest

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

theorem pairedRecord_valueId (tau d n v : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    seedValueId (pairedRecord tau d n v a b)=seedValueId (seedNodeView tau d n v a) := by
  cases h with
  | hash h => rfl
  | leaf k m hs => cases hs <;> simp [seedValueId,pairedRecord,seedNodeView,pairedNode,
      viewNode,pairedSlot,viewSlot,NodeV3.value]
  | ext k m hc => rfl
  | branch m hv hcs =>
    cases hv with
    | none => rfl
    | some hs => cases hs <;> simp [seedValueId,pairedRecord,seedNodeView,pairedNode,
        viewNode,pairedSlot,viewSlot,NodeV3.value]

mutual
theorem pairedNodes_valueIds : ∀(tau d n v : Nat){a b : PTrie},WriteTreePair a b →
    (pairedNodes tau d n v a b).filterMap seedValueId=
      (seedNodesT tau d n v a).filterMap seedValueId
  | _,_,_,_,_,_,.hash _ => rfl
  | tau,d,n,v,_,_,.leaf k m h => by
    simp only [pairedNodes,seedNodesT,List.filterMap_cons,pairedRecord_valueId tau d n v (.leaf k m h)]
  | tau,d,n,v,_,_,.ext k m h => by
    simp only [pairedNodes,seedNodesT,List.filterMap_cons,pairedRecord_valueId tau d n v (.ext k m h),
      pairedNodes_valueIds tau (d+1) (n+1) v h]
  | tau,d,n,v,_,_,.branch m h hs => by
    simp only [pairedNodes,seedNodesT,List.filterMap_cons,pairedRecord_valueId tau d n v (.branch m h hs),
      pairedChildNodes_valueIds tau (d+1) (n+1) _ hs]
theorem pairedChildNodes_valueIds : ∀(tau d n v : Nat){a b : Kids},WriteKidsPair a b →
    (pairedChildNodes tau d n v a b).filterMap seedValueId=
      (seedKidsT tau d n v a).filterMap seedValueId
  | _,_,_,_,_,_,.nil => rfl
  | tau,d,n,v,_,_,.none h => by
    simpa only [pairedChildNodes,seedKidsT] using pairedChildNodes_valueIds tau d n v h
  | tau,d,n,v,_,_,.some h hs => by
    simp only [pairedChildNodes,seedKidsT,List.filterMap_append]
    rw [pairedNodes_valueIds tau d n v h,pairedChildNodes_valueIds tau d _ _ hs]
end

theorem pairedForest_valueIds : ∀(tau n v : Nat)(pairs : List (PTrie×PTrie)),
    (∀p∈pairs,WriteTreePair p.1 p.2) →
    (pairedForest tau n v pairs).filterMap seedValueId=
      List.range' v (forestBytes (pairs.map Prod.fst)).length
  | _,_,_,[],_ => by simp [pairedForest,forestBytes]
  | tau,n,v,(pre,post)::rest,h => by
    simp only [pairedForest,List.filterMap_append]
    rw [pairedNodes_valueIds tau 0 n v (h (pre,post) (by simp)),seedNodesT_valueIds]
    rw [pairedForest_valueIds _ _ _ rest (fun p hp => h p (by simp [hp]))]
    simp only [List.map_cons,forestBytes,List.flatMap_cons,List.length_append]
    simpa using (List.range'_append (s:=v) (m:=(valsOf pre).length)
      (n:=(List.flatMap valsOf (List.map Prod.fst rest)).length) (step:=1))

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
