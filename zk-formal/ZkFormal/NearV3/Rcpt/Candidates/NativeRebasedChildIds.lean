import ZkFormal.NearV3.Rcpt.Candidates.NativeRebasedDepths
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayByteSize
import ZkFormal.NearV3.Render.Ups.SourceCidBytes
import ZkFormal.NearV3.Candidates.NativeNodeChildIds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

theorem write_tsize {a b : PTrie} (h : WriteTreePair a b) : tsize a=tsize b :=
  (paired_occurrences h).length

theorem write_kid_ids (n : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    kidIds (viewKid n a)=kidIds (viewKid n b) := by
  cases h <;> rfl

theorem write_kids_ids : ∀(n : Nat){a b : Kids},WriteKidsPair a b→
    (viewKids n a).flatMap kidIds=(viewKids n b).flatMap kidIds
  | _,_,_,.nil => rfl
  | n,_,_,.none h => by simpa only [viewKids,List.flatMap_cons,kidIds,List.nil_append] using write_kids_ids n h
  | n,_,_,.some h hs => by
    simp only [viewKids,List.flatMap_cons,write_kid_ids n h]
    rw [write_tsize h,write_kids_ids _ hs]

/-- Actual receipt updates preserve every byte position's child occurrence ID. -/
theorem write_window_ids (n v v' : Nat) {a b : PTrie} (h : WriteTreePair a b) :
    windowIds (viewNode n v a)=windowIds (viewNode n v' b) := by
  cases h with
  | hash => rfl
  | leaf k m hs =>
    cases hs <;> simp [viewNode,windowIds,NodeV3.ser,viewSlot,NSlot3.bytes,
      List.length_append,List.length_map,NearSpec.u32,NearSpec.leN_length]
  | ext k m hc => simp only [viewNode,windowIds,write_kid_ids _ hc]
  | branch m hv hs =>
    cases hv <;> simp only [viewNode,windowIds,Option.map_none,Option.map_some,
      Option.isSome_none,Option.isSome_some,write_kids_ids _ hs]

mutual
theorem write_node_window_lists : ∀(tau d n v v' : Nat){a b : PTrie},WriteTreePair a b→
    (seedNodesT tau d n v a).map (fun s=>windowIds s.v)=
      (seedNodesT tau d n v' b).map (fun s=>windowIds s.v)
  | _,_,_,_,_,_,_,.hash _ => rfl
  | tau,d,n,v,v',_,_,.leaf k m h => by
    simp only [seedNodesT,List.map_cons,List.map_nil,seedNodeView]
    rw [write_window_ids n v v' (.leaf k m h)]
  | tau,d,n,v,v',_,_,.ext k m h => by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_window_ids n v v' (.ext k m h),write_node_window_lists tau (d+1) (n+1) v v' h]
  | tau,d,n,v,v',_,_,.branch m h hs => by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_window_ids n v v' (.branch m h hs),write_kid_window_lists tau (d+1) (n+1) _ _ hs]
theorem write_kid_window_lists : ∀(tau d n v v' : Nat){a b : Kids},WriteKidsPair a b→
    (seedKidsT tau d n v a).map (fun s=>windowIds s.v)=
      (seedKidsT tau d n v' b).map (fun s=>windowIds s.v)
  | _,_,_,_,_,_,_,.nil => rfl
  | tau,d,n,v,v',_,_,.none h => by simpa only [seedKidsT] using write_kid_window_lists tau d n v v' h
  | tau,d,n,v,v',_,_,.some h hs => by
    simp only [seedKidsT,List.map_append]
    rw [write_node_window_lists tau d n v v' h,write_tsize h,write_kid_window_lists tau d _ _ _ hs]
end

theorem replay_forest_window_lists : ∀(rs : List ReplayTree)(tau n v v' : Nat),
    (∀r∈rs,r.Valid)→
    (forestNodes tau n v (rs.map ReplayTree.pre)).map (fun s=>windowIds s.v)=
      (forestNodes tau n v' (rs.map ReplayTree.post)).map (fun s=>windowIds s.v)
  | [],_,_,_,_,_ => rfl
  | r::rs,tau,n,v,v',h => by
    have hp:=(h r (by simp)).forget.skeleton
    simp only [List.map_cons,forestNodes,List.map_append]
    rw [write_node_window_lists tau 0 n v v' hp,write_tsize hp]
    rw [replay_forest_window_lists rs (tau+1) _ _ _ (fun r hr=>h r (by simp [hr]))]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
