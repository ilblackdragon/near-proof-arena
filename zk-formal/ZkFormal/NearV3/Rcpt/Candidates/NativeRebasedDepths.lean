import ZkFormal.NearV3.Rcpt.Candidates.NativeForestInputs

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render.UpsGen Assembly

mutual
/-- Receipt writes preserve every occurrence depth, independent of payload and
of the node/value index offsets used to materialize the two forests. -/
theorem write_node_depths : ∀(tau d n v n' v' : Nat){a b : PTrie},WriteTreePair a b→
    (seedNodesT tau d n v a).map NodeS3.depth=(seedNodesT tau d n' v' b).map NodeS3.depth
  | _,_,_,_,_,_,_,_,.hash _ => rfl
  | _,_,_,_,_,_,_,_,.leaf _ _ _ => rfl
  | tau,d,n,v,n',v',_,_,.ext k m h => by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_node_depths tau (d+1) (n+1) v (n'+1) v' h]
  | tau,d,n,v,n',v',_,_,.branch m h hs => by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_kid_depths tau (d+1) (n+1) _ (n'+1) _ hs]
theorem write_kid_depths : ∀(tau d n v n' v' : Nat){a b : Kids},WriteKidsPair a b→
    (seedKidsT tau d n v a).map NodeS3.depth=(seedKidsT tau d n' v' b).map NodeS3.depth
  | _,_,_,_,_,_,_,_,.nil => rfl
  | tau,d,n,v,n',v',_,_,.none h => by simpa only [seedKidsT] using write_kid_depths tau d n v n' v' h
  | tau,d,n,v,n',v',_,_,.some h hs => by
    simp only [seedKidsT,List.map_append]
    rw [write_node_depths tau d n v n' v' h,write_kid_depths tau d _ _ _ _ hs]
end

theorem replay_forest_depths : ∀(rs : List ReplayTree)(tau n v n' v' : Nat),
    (∀r∈rs,r.Valid)→
    (forestNodes tau n v (rs.map ReplayTree.pre)).map NodeS3.depth=
      (forestNodes tau n' v' (rs.map ReplayTree.post)).map NodeS3.depth
  | [],_,_,_,_,_,_ => rfl
  | r::rs,tau,n,v,n',v',h => by
    simp only [List.map_cons,forestNodes,List.map_append]
    rw [write_node_depths tau 0 n v n' v' (h r (by simp)).forget.skeleton]
    rw [replay_forest_depths rs (tau+1) _ _ _ _ (fun r hr=>h r (by simp [hr]))]

/-- Updating old-record digests preserves the rebased forest's exact depth at
all globally indexed providers. -/
theorem replay_updated_depth_at (rs : List ReplayTree) (h : ∀r∈rs,r.Valid)
    (u : Inputs) {i : Nat} {a b : NodeS3}
    (ha : (records u (forestNodes 0 0 0 (rs.map ReplayTree.pre)))[i]?=some a)
    (hb : (forestNodes 0 0 0 (rs.map ReplayTree.post))[i]?=some b) :
    a.depth=b.depth := by
  have he : (records u (forestNodes 0 0 0 (rs.map ReplayTree.pre))).map NodeS3.depth=
      (forestNodes 0 0 0 (rs.map ReplayTree.post)).map NodeS3.depth := by
    simpa only [records,List.map_map,Function.comp_def,record] using replay_forest_depths rs 0 0 0 0 0 h
  have hi:=congrArg (fun xs=>xs[i]?) he
  simpa only [List.getElem?_map,ha,hb,Option.map_some,Option.some.injEq] using hi

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
