import ZkFormal.NearV3.Rcpt.Render.Srcp.TrafficPath

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near

/-- Every honest block has exactly the semantic source-proof bus messages. -/
theorem block_messages (B : SrcpB) (z bb : Nat) (sd : Bool)
    (hr : B.root.length = 32) (hl : B.leaf.length = 32)
    (hp : ∀ it ∈ B.path, it.sib.length = 32 ∧ it.acc.length = 32) :
    (kinds B).flatMap (fun k => rowN (frame B z k).cell bb sd) = srcpBlockMsgs B bb sd := by
  simp only [kinds, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.flatMap_map, Function.comp_def, frame, root_messages B z bb sd hr,
    leaf_messages B z bb sd hl, srcpBlockMsgs]
  congr 1
  rw [List.flatMap_assoc]
  have hh : (List.range B.path.length).flatMap (fun i =>
      (List.range 64).flatMap (fun o => rowN (pathFrame B z i o).cell bb sd)) =
      (List.range B.path.length).flatMap (fun i => srcpItemMsgs (B.path.getD i default) bb sd) := by
    apply flatMap_congr'
    intro i hi
    have hii := List.mem_range.mp hi
    have hm : B.path.getD i default ∈ B.path := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hii]
      exact List.getElem_mem hii
    exact path_messages B z i bb sd (hp _ hm).2 (hp _ hm).1
  simp only [List.flatMap_map, Function.comp_def, frame] 
  rw [hh]
  exact flatMap_getD_all default (fun it => srcpItemMsgs it bb sd) B.path

end ZkFormal.NearV3.Render.SrcpGen
