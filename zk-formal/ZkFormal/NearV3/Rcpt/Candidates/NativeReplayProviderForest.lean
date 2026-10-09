import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayProviderNode

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

private theorem provider_optional_count {a b : Option Slot} (h : Option.Rel WriteSlotPair a b) :
    (ZkFormal.NearV3.optSlotVal a).length=(ZkFormal.NearV3.optSlotVal b).length := by
  cases h with
  | none=>rfl
  | some h=>cases h <;> rfl

private theorem provider_value_count {a b : PTrie} (h : WriteTreePair a b) :
    (ZkFormal.NearV3.valsOf a).length=(ZkFormal.NearV3.valsOf b).length := by
  simpa only [native_valsOf_eq] using write_value_count h

mutual
theorem write_provider_nodes : ∀(tau d n v : Nat){a b : PTrie},WriteTreePair a b→
    (seedNodesT tau d n v a).map (fun s=>providerNode s.v)=
      (seedNodesT tau d n v b).map (fun s=>providerNode s.v)
  | _,_,_,_,_,_,.hash _=>rfl
  | tau,d,n,v,_,_,.leaf k m h=>by
    simp only [seedNodesT,List.map_cons,List.map_nil,seedNodeView]
    rw [write_providerNode n v (.leaf k m h)]
  | tau,d,n,v,_,_,.ext k m h=>by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_providerNode n v (.ext k m h),write_provider_nodes tau (d+1) (n+1) v h]
  | tau,d,n,v,_,_,.branch m h hs=>by
    simp only [seedNodesT,List.map_cons,seedNodeView]
    rw [write_providerNode n v (.branch m h hs),provider_optional_count h,
      write_provider_kids tau (d+1) (n+1) _ hs]
theorem write_provider_kids : ∀(tau d n v : Nat){a b : Kids},WriteKidsPair a b→
    (seedKidsT tau d n v a).map (fun s=>providerNode s.v)=
      (seedKidsT tau d n v b).map (fun s=>providerNode s.v)
  | _,_,_,_,_,_,.nil=>rfl
  | tau,d,n,v,_,_,.none h=>by simpa only [seedKidsT] using write_provider_kids tau d n v h
  | tau,d,n,v,_,_,.some h hs=>by
    simp only [seedKidsT,List.map_append]
    rw [write_provider_nodes tau d n v h,write_tsize h,provider_value_count h,
      write_provider_kids tau d _ _ hs]
end

theorem replay_provider_nodes : ∀(rs : List ReplayTree)(tau n v : Nat),
    (∀r∈rs,r.Valid)→
    (forestNodes tau n v (rs.map ReplayTree.pre)).map (fun s=>providerNode s.v)=
      (forestNodes tau n v (rs.map ReplayTree.post)).map (fun s=>providerNode s.v)
  | [],_,_,_,_=>rfl
  | r::rs,tau,n,v,h=>by
    have hp:=(h r (by simp)).forget.skeleton
    simp only [List.map_cons,forestNodes,List.map_append]
    rw [write_provider_nodes tau 0 n v hp,write_tsize hp,provider_value_count hp]
    rw [replay_provider_nodes rs (tau+1) _ _ (fun r hr=>h r (by simp [hr]))]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
