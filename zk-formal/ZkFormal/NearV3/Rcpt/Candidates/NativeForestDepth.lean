import ZkFormal.NearV3.Rcpt.Candidates.NativeNodeMetadata
import ZkFormal.NearV3.Assembly.ForestViews

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3.Render.UpsGen

mutual
theorem depths_bound : ∀(t : PTrie)(d x : Nat),x∈depsT d t → x<d+theight t
  | .hash _,_,_,h => by simp [depsT] at h
  | .leaf ..,d,x,h => by simp [depsT] at h; subst x; simp [theight]
  | .ext k c m,d,x,h => by
    simp only [depsT,List.mem_cons] at h
    rcases h with rfl|h
    · simp only [theight]; omega
    · have hh:=depths_bound c (d+1) x h; simp only [theight]; omega
  | .branch v cs m,d,x,h => by
    simp only [depsT,List.mem_cons] at h
    rcases h with rfl|h
    · simp only [theight]; omega
    · have hh:=kid_depths_bound cs (d+1) x h; simp only [theight]; omega
theorem kid_depths_bound : ∀(cs : Kids)(d x : Nat),x∈kdepsT d cs → x<d+kheight cs
  | .nil,_,_,h => by simp [kdepsT] at h
  | .none cs,d,x,h => kid_depths_bound cs d x h
  | .some c cs,d,x,h => by
    simp only [kdepsT,List.mem_append] at h
    rcases h with h|h
    · have hh:=depths_bound c d x h
      have hm:=Nat.le_max_left (theight c) (kheight cs)
      simp only [kheight]; omega
    · have hh:=kid_depths_bound cs d x h
      have hm:=Nat.le_max_right (theight c) (kheight cs)
      simp only [kheight]; omega
end

theorem seed_depth_bound (tau d n v : Nat) (t : PTrie) (s : NodeS3)
    (hs : s∈seedNodesT tau d n v t) : s.depth<d+theight t := by
  have hm : s.depth∈(seedNodesT tau d n v t).map NodeS3.depth:=List.mem_map.mpr ⟨s,hs,rfl⟩
  rw [seedNodesT_depths] at hm
  exact depths_bound t d s.depth hm

theorem native_seed_depth (tau n v : Nat) (t : PTrie)
    (hf : ∀k,fdepth t k≤trieFuel) (s : NodeS3) (hs : s∈seedNodesT tau 0 n v t) :
    s.depth<400 := by
  have hh:=theight_le_of_fdepth hf
  have hd:=seed_depth_bound tau 0 n v t s hs
  change theight t≤400 at hh
  omega

theorem native_forest_depth : ∀(ts : List PTrie)(tau n v : Nat),
    (∀t∈ts,∀k,fdepth t k≤trieFuel) →
    ∀s∈Assembly.forestNodes tau n v ts,s.depth<400
  | [],_,_,_,_,_,hs => by simp [Assembly.forestNodes] at hs
  | t::ts,tau,n,v,h,s,hs => by
    simp only [Assembly.forestNodes,List.mem_append] at hs
    rcases hs with hs|hs
    · exact native_seed_depth tau n v t (h t (by simp)) s hs
    · exact native_forest_depth ts (tau+1) (n+tsize t) (v+(valsOf t).length)
        (fun t ht => h t (by simp [ht])) s hs

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
