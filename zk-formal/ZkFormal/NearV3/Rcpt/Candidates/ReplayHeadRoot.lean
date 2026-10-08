import ZkFormal.NearV3.Rcpt.Candidates.NativeReaderRootId
import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayHeadKeys

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near Render Render.UpsGen Assembly

/-- Exact post-replay root at each HEAD index. The HEAD IDs are allocated from
the original forest, and receipt replay preserves those occurrence offsets. -/
theorem replay_head_root : ∀(rs : List ReplayTree)(tau n v i : Nat)(root : OccurrenceAddress),
    (∀r∈rs,r.Valid)→forestRootAt n v (rs.map ReplayTree.post) i=some root→
    ∃h,(forestWalkHeads tau n (rs.map (fun r=>(r.pre,r.post))))[i]?=some h ∧
      h.tau=tau+i ∧ h.rid=root.nid ∧ h.post=root.tree.hashOf.map UInt8.toNat
  | [],_,_,_,_,_,_,hr=>by simp [forestRootAt] at hr
  | r::rs,tau,n,v,0,root,hv,hr=>by
    simp only [List.map_cons,forestRootAt,Option.some.injEq] at hr
    subst root
    exact ⟨_,rfl,by simp,rfl,rfl⟩
  | r::rs,tau,n,v,i+1,root,hv,hr=>by
    have hp:=(hv r (by simp)).forget.skeleton
    have hn:=write_tsize hp
    have hr' : forestRootAt (n+tsize r.post) (v+(valsOf r.post).length) (rs.map ReplayTree.post) i=some root:=hr
    obtain ⟨h,hget,ht,hi,hpost⟩:=replay_head_root rs (tau+1) (n+tsize r.post) _ i root
      (fun r hr=>hv r (by simp [hr])) hr'
    refine ⟨h,?_,by omega,hi,hpost⟩
    simpa only [List.map_cons,forestWalkHeads,List.getElem?_cons_succ,hn] using hget

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
