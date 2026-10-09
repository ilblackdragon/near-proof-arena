import ZkFormal.NearV3.Rcpt.Candidates.NativeRootHeader

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near Render Render.UpsGen Assembly

theorem forest_head_root_records : ∀(pairs : List (PTrie×PTrie))(tau n : Nat),
    headRecvs (forestWalkHeads tau n pairs) B_ROOT=nativeInputRoots tau (pairs.map Prod.fst)
  | [],_,_=>rfl
  | (pre,post)::rest,tau,n=>by
    change ([tau]++pre.hashOf.map UInt8.toNat)::
      headRecvs (forestWalkHeads (tau+1) (n+tsize pre) rest) B_ROOT=_
    rw [forest_head_root_records]
    rfl

/-- Replay HEADs receive exactly the original native input roots, including every implicit transition. -/
theorem replay_head_root_records (m : MainExecutionV3) (steps : List ImplicitStepV3)
    (oldPost : PTrie) (writes : List (List Nat×Bytes)) :
    headRecvs (forestWalkHeads 0 0 ((nativeReplayForest m steps oldPost writes).map
      (fun r=>(r.pre,r.post)))) B_ROOT=
      nativeInputRoots 0 (m.pre::steps.map ImplicitStepV3.pre) := by
  rw [forest_head_root_records]
  congr 1
  simp only [List.map_map,Function.comp_def,nativeReplayForest_pre]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
