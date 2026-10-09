import ZkFormal.NearV3.Rcpt.Candidates.NodePairedWf

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

def pairedRecord (tau depth nid vid : Nat) (pre post : PTrie) : NodeS3 :=
  {seedNodeView tau depth nid vid pre with v:=pairedNode nid vid pre post}

mutual
/-- The native pre-tree determines IDs; post payloads are paired recursively. -/
def pairedNodes (tau : Nat) : Nat→Nat→Nat→PTrie→PTrie→List NodeS3
  | _,_,_,.hash _,_ => []
  | d,n,v,.leaf k s m,post => [pairedRecord tau d n v (.leaf k s m) post]
  | d,n,v,.ext k c m,.ext _ c' _ =>
      pairedRecord tau d n v (.ext k c m) (.ext k c' m)::pairedNodes tau (d+1) (n+1) v c c'
  | d,n,v,.branch sv cs m,.branch sv' ds _ =>
      pairedRecord tau d n v (.branch sv cs m) (.branch sv' ds m)::
        pairedChildNodes tau (d+1) (n+1) (v+(optSlotVal sv).length) cs ds
  | d,n,v,pre,_ => seedNodesT tau d n v pre
def pairedChildNodes (tau : Nat) : Nat→Nat→Nat→Kids→Kids→List NodeS3
  | _,_,_,.nil,_ => []
  | d,n,v,.none cs,.none ds => pairedChildNodes tau d n v cs ds
  | d,n,v,.some c cs,.some c' ds =>
      pairedNodes tau d n v c c'++pairedChildNodes tau d (n+tsize c) (v+(valsOf c).length) cs ds
  | d,n,v,cs,_ => seedKidsT tau d n v cs
end

mutual
theorem pairedNodes_pre : ∀(tau d n v : Nat){a b : PTrie},WriteTreePair a b →
    (pairedNodes tau d n v a b).map (fun s => s.v.ser false)=
      (seedNodesT tau d n v a).map (fun s => s.v.ser false)
  | _,_,_,_,_,_,.hash _ => rfl
  | tau,d,n,v,_,_,.leaf k m h => by
    simp only [pairedNodes,seedNodesT,List.map_cons,List.map_nil,pairedRecord,seedNodeView]
    rw [pairedNode_pre n v (.leaf k m h)]
  | tau,d,n,v,_,_,.ext k m h => by
    simp only [pairedNodes,seedNodesT,List.map_cons,pairedRecord,seedNodeView]
    rw [pairedNode_pre n v (.ext k m h),pairedNodes_pre tau (d+1) (n+1) v h]
  | tau,d,n,v,_,_,.branch m h hs => by
    simp only [pairedNodes,seedNodesT,List.map_cons,pairedRecord,seedNodeView]
    rw [pairedNode_pre n v (.branch m h hs),pairedChildNodes_pre tau (d+1) (n+1) _ hs]
theorem pairedChildNodes_pre : ∀(tau d n v : Nat){a b : Kids},WriteKidsPair a b →
    (pairedChildNodes tau d n v a b).map (fun s => s.v.ser false)=
      (seedKidsT tau d n v a).map (fun s => s.v.ser false)
  | _,_,_,_,_,_,.nil => rfl
  | tau,d,n,v,_,_,.none h => by simpa only [pairedChildNodes,seedKidsT] using pairedChildNodes_pre tau d n v h
  | tau,d,n,v,_,_,.some h hs => by
    simp only [pairedChildNodes,seedKidsT,List.map_append]
    rw [pairedNodes_pre tau d n v h,pairedChildNodes_pre tau d _ _ hs]
end

def pairedForest : Nat→Nat→Nat→List (PTrie×PTrie)→List NodeS3
  | _,_,_,[] => []
  | tau,n,v,(pre,post)::rest => pairedNodes tau 0 n v pre post++
      pairedForest (tau+1) (n+tsize pre) (v+(valsOf pre).length) rest

theorem pairedForest_pre : ∀(tau n v : Nat)(pairs : List (PTrie×PTrie)),
    (∀p∈pairs,WriteTreePair p.1 p.2) →
    (pairedForest tau n v pairs).map (fun s => s.v.ser false)=
      (forestNodes tau n v (pairs.map Prod.fst)).map (fun s => s.v.ser false)
  | _,_,_,[],_ => rfl
  | tau,n,v,(pre,post)::rest,h => by
    simp only [pairedForest,forestNodes,List.map_cons,List.map_append]
    rw [pairedNodes_pre tau 0 n v (h (pre,post) (by simp))]
    rw [pairedForest_pre _ _ _ rest (fun p hp => h p (by simp [hp]))]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
