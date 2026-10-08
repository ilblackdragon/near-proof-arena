import ZkFormal.NearV3.Render.Ups.BranchWindowInput
import ZkFormal.NearV3.Render.Ups.TreeEdge

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- First/last native slots coincide with first/last occupied serialization windows. -/
theorem boundary_cid_prefix (kids : List NKid) (sd : Nat) (hk : kids.length=16)
    (hs : sd=0 ∨ sd=1) (kid : NKid) (hp : kids[edgeSlot sd]?=some kid) (hn : kid≠.none) :
    (branchCidBytes (kids.take (edgeSlot sd))).length=
      32*(if sd==1 then (kids.filter (fun k=>k≠.none)).length-1 else 0) := by
  rcases hs with rfl|rfl
  · simp [edgeSlot,branchCidBytes]
  · have he := edge_decompose 1 kids hk
    have hd : kids.getD 15 .none=kid := by
      simpa only [List.getD_eq_getElem?_getD,edgeSlot,ite_true,hp,Option.getD_some] using
        (show kids.getD (edgeSlot 1) .none=kid from by
          simp only [List.getD_eq_getElem?_getD,hp,Option.getD_some])
    simp only [edgeKids,edgeRest,edgeSlot,ite_true,hd] at he
    have hc := congrArg (fun ks : List NKid=>(ks.filter (fun k=>k≠.none)).length) he
    have hn' : decide (kid≠NKid.none)=true := by simp [hn]
    simp only [List.filter_append,List.filter_cons,List.filter_nil,hn',decide_true,ite_true,
      List.length_append,List.length_cons,List.length_nil] at hc
    simp only [edgeSlot,ite_true,beq_self_eq_true,branchCidBytes_length]
    omega
end ZkFormal.NearV3.Render.UpsGen
