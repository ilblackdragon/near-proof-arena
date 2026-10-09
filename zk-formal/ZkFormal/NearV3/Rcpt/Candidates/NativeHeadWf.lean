import ZkFormal.NearV3.Rcpt.Candidates.NativeReplayHeadKeys
import ZkFormal.NearV3.Rcpt.Candidates.NativeForestByteBounds
import ZkFormal.NearV3.Render.HeadRender

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec ZkFormal.Near ZkFormal.Algebra Render Render.UpsGen Assembly

private theorem target_le (t : PTrie) (n : Nat) : viewTarget n t≤n+tsize t := by
  by_cases hn : isNode t=true
  · exact Nat.le_of_lt (target_bound t n hn).2
  · cases t <;> simp_all [isNode,viewTarget,tsize,occs]

/-- Full HEAD scalar and digest validity for one indexed native forest. Post
roots may be receipt replay roots rather than structural scheduler outputs. -/
theorem forest_head_wf : ∀(pairs : List (PTrie×PTrie))(tau n : Nat),
    tau+pairs.length<Algebra.P → n+((pairs.map Prod.fst).flatMap occs).length<Algebra.P →
    (∀a b,(a,b)∈pairs→a.wf=true ∧ b.wf=true ∧ (nodeEnc a).length<Algebra.P) →
    HeadWf (forestWalkHeads tau n pairs)
  | [],_,_,_,_,_=>by constructor <;> simp [forestWalkHeads]
  | (a,b)::pairs,tau,n,ht,hn,hw=>by
    have hab:=hw a b (by simp)
    have hh:=(ZkFormal.Near.Prune.hashOf_length a hab.1)
    have hb:=(ZkFormal.Near.Prune.hashOf_length b hab.2.1)
    have hnr : n+tsize a+((pairs.map Prod.fst).flatMap occs).length<Algebra.P := by
      simpa only [List.map_cons,List.flatMap_cons,List.length_append,tsize,Nat.add_assoc] using hn
    have htr : tau+1+pairs.length<Algebra.P := by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht
    have ih:=forest_head_wf pairs (tau+1) (n+tsize a) htr hnr (fun x y h=>hw x y (by simp [h]))
    constructor
    · intro h hm
      simp only [forestWalkHeads,List.mem_cons] at hm
      rcases hm with rfl|hm
      · simpa only [List.length_map] using And.intro hh hb
      · exact ih.len h hm
    · intro h hm
      simp only [forestWalkHeads,List.mem_cons] at hm
      rcases hm with rfl|hm
      · dsimp only
        have hv:=target_le a n
        refine ⟨by omega,by omega,hab.2.2,by omega,by change 0<Algebra.P;decide,native_bytes_small _,native_bytes_small _⟩
      · exact ih.canon h hm

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
