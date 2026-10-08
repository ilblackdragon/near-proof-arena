import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeMetadata
import ZkFormal.NearV3.Assembly.ForestViews

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.NearV3.Render.UpsGen

mutual
theorem seed_index_res : ∀(t : PTrie)(tau d n v i : Nat)(s : NodeS3),
    (seedNodesT tau d n v t)[i]?=some s → s.resOk (n+i)
  | .hash _,_,_,_,_,_,_,h => by simp [seedNodesT] at h
  | .leaf k sl m,tau,d,n,v,i,s,h => by
    cases i with
    | zero => simp [seedNodesT] at h; subst s; exact seed_res tau d n v _
    | succ i => simp [seedNodesT] at h
  | .ext k c m,tau,d,n,v,i,s,h => by
    cases i with
    | zero => simp [seedNodesT] at h; subst s; exact seed_res tau d n v _
    | succ i =>
      simp only [seedNodesT,List.getElem?_cons_succ] at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using seed_index_res c tau (d+1) (n+1) v i s h
  | .branch sl cs m,tau,d,n,v,i,s,h => by
    cases i with
    | zero => simp [seedNodesT] at h; subst s; exact seed_res tau d n v _
    | succ i =>
      simp only [seedNodesT,List.getElem?_cons_succ] at h
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        seed_kid_index_res cs tau (d+1) (n+1) (v+(optSlotVal sl).length) i s h
theorem seed_kid_index_res : ∀(cs : Kids)(tau d n v i : Nat)(s : NodeS3),
    (seedKidsT tau d n v cs)[i]?=some s → s.resOk (n+i)
  | .nil,_,_,_,_,_,_,h => by simp [seedKidsT] at h
  | .none cs,tau,d,n,v,i,s,h => seed_kid_index_res cs tau d n v i s h
  | .some c cs,tau,d,n,v,i,s,h => by
    simp only [seedKidsT] at h
    by_cases hi : i<(seedNodesT tau d n v c).length
    · rw [List.getElem?_append_left hi] at h
      exact seed_index_res c tau d n v i s h
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at h
      rw [seedNodesT_length] at h hi
      have hr:=seed_kid_index_res cs tau d (n+tsize c) (v+(valsOf c).length) (i-tsize c) s h
      have he : n+tsize c+(i-tsize c)=n+i := by omega
      simpa only [he] using hr
end

theorem target_bound : ∀(t : PTrie)(n : Nat),isNode t=true →
    n≤viewTarget n t ∧ viewTarget n t<n+tsize t
  | .hash _,_,h => by simp [isNode] at h
  | .leaf k s m,n,_ => by simp [viewTarget,tsize,occs]
  | .branch v cs m,n,_ => by simp only [viewTarget,tsize,occs,List.length_cons]; omega
  | .ext k c m,n,_ => by
    cases k with
    | cons a k => simp only [viewTarget,tsize,occs,List.length_cons]; omega
    | nil =>
      by_cases hc : isNode c=true
      · have h:=target_bound c (n+1) hc
        simp only [viewTarget,hc,ite_true,tsize,occs,List.length_cons]
        simp only [tsize] at h
        omega
      · simp only [viewTarget,hc,Bool.false_eq_true,ite_false,tsize,occs,List.length_cons]; omega

theorem forest_index_res : ∀(ts : List PTrie)(tau n v i : Nat)(s : NodeS3),
    (Assembly.forestNodes tau n v ts)[i]?=some s → s.resOk (n+i)
  | [],_,_,_,_,_,h => by simp [Assembly.forestNodes] at h
  | t::ts,tau,n,v,i,s,h => by
    simp only [Assembly.forestNodes] at h
    by_cases hi : i<(seedNodesT tau 0 n v t).length
    · rw [List.getElem?_append_left hi] at h
      exact seed_index_res t tau 0 n v i s h
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at h
      rw [seedNodesT_length] at h hi
      have hr:=forest_index_res ts (tau+1) (n+tsize t) (v+(valsOf t).length) (i-tsize t) s h
      have he : n+tsize t+(i-tsize t)=n+i := by omega
      simpa only [he] using hr

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
