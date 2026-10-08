import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayProviderKeys

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

/-- HEAD request identities ignore post digests but retain the resolved root. -/
theorem head_keys_fst : ∀(as bs : List (PTrie×PTrie))(tau n : Nat),
    as.map Prod.fst=bs.map Prod.fst→
    headEdgeKeys (forestWalkHeads tau n as)=headEdgeKeys (forestWalkHeads tau n bs)
  | [],[],_,_,_=>rfl
  | [],_::_,_,_,h=>by simp at h
  | _::_,[],_,_,h=>by simp at h
  | (a,ap)::as,(b,bp)::bs,tau,n,h=>by
    have hh:=List.cons.inj h
    have hab : a=b:=hh.1
    subst b
    simp only [forestWalkHeads,headEdgeKeys,List.map_cons,headEdgeKey]
    exact congrArg (List.cons _) (head_keys_fst as bs (tau+1) (n+tsize a) hh.2)

theorem replay_head_keys : ∀(rs : List ReplayTree)(tau n : Nat),
    (∀r∈rs,r.Valid)→
    headEdgeKeys (forestWalkHeads tau n (rs.map (fun r=>(r.pre,r.post))))=
      headEdgeKeys (forestWalkHeads tau n (rs.map (fun r=>(r.post,r.post))))
  | [],_,_,_=>rfl
  | r::rs,tau,n,h=>by
    have hp:=(h r (by simp)).forget.skeleton
    simp only [List.map_cons,forestWalkHeads,headEdgeKeys,List.map_cons,headEdgeKey]
    rw [write_viewTarget n hp,write_tsize hp]
    exact congrArg (List.cons _) (replay_head_keys rs (tau+1) _ (fun r hr=>h r (by simp [hr])))

/-- Actual original/rebased pairs may have different final trees: only their
prestate arrays must be the two sides of the same receipt replay. -/
theorem replay_actual_head_keys (rs : List ReplayTree) (as bs : List (PTrie×PTrie))
    (ha : as.map Prod.fst=rs.map ReplayTree.pre)
    (hb : bs.map Prod.fst=rs.map ReplayTree.post) (hv : ∀r∈rs,r.Valid) :
    headEdgeKeys (forestWalkHeads 0 0 as)=headEdgeKeys (forestWalkHeads 0 0 bs) := by
  have h1:=head_keys_fst as (rs.map (fun r=>(r.pre,r.post))) 0 0 (by simpa only [List.map_map,Function.comp_def] using ha)
  have h2:=head_keys_fst bs (rs.map (fun r=>(r.post,r.post))) 0 0 (by simpa only [List.map_map,Function.comp_def] using hb)
  rw [h1,h2]
  exact replay_head_keys rs 0 0 hv

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
